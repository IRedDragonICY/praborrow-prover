use crate::ProofError;
use crate::VerificationToken;
use alloc::boxed::Box;
use async_trait::async_trait;

/// Represents a value retrieved from a field.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum FieldValue {
    Int(i64),
    UInt(u64),
    Bool(bool),
}

/// Interface for providing field values to the backend.
pub trait FieldValueProvider: Send + Sync {
    /// Gets the value of a field by name.
    fn get_field_value(&self, name: &str) -> Result<FieldValue, ProofError>;
}

/// Abstract interface for a solver backend.
#[async_trait]
pub trait SolverBackend: Send + Sync {
    /// Verifies a set of invariants against the provided field values.
    async fn verify(
        &self,
        invariants: &[&str],
        provider: &dyn FieldValueProvider,
    ) -> Result<VerificationToken, ProofError>;
}

#[cfg(feature = "z3-backend")]
pub mod z3_backend {
    use super::*;
    use crate::parser::ExpressionParser;
    use crate::parser::ExprVisitor;
    use crate::parser::ExprKind;
    use crate::parser::ComparisonOp;
    use crate::parser::BitwiseOp;
    use crate::parser::ArithmeticOp;
    use z3::{Config, Context, SatResult, Solver, ast};

    pub struct Z3Backend {
        context: Context,
    }

    impl Z3Backend {
        pub fn new() -> Result<Self, ProofError> {
            let config = Config::new();
            let context = Context::new(&config);
            Ok(Self { context })
        }
    }

    #[async_trait]
    impl SolverBackend for Z3Backend {
        async fn verify(
            &self,
            invariants: &[&str],
            provider: &dyn FieldValueProvider,
        ) -> Result<VerificationToken, ProofError> {
            // Z3 is not thread-safe and not async, so we must be careful.
            // For now, we run it synchronously in the async block.
            // In a real constrained environment, we might offload to a blocking thread.
            
            let solver = Solver::new(&self.context);
            
            for inv in invariants {
                let expr = ExpressionParser::parse(inv)?;
                let mut generator = Z3AstGenerator::new(&self.context, provider);
                let assertion = generator.generate(&expr)?;
                solver.assert(&assertion);
            }

            match solver.check() {
                SatResult::Sat => Ok(VerificationToken::new()),
                SatResult::Unsat => Err(ProofError::InvariantViolated(
                    "Solver proved invariant cannot be satisfied".to_string(),
                )),
                SatResult::Unknown => Err(ProofError::Unknown),
            }
        }
    }

    struct Z3AstGenerator<'ctx, 'prov> {
        ctx: &'ctx Context,
        provider: &'prov dyn FieldValueProvider,
    }

    impl<'ctx, 'prov> Z3AstGenerator<'ctx, 'prov> {
        fn new(ctx: &'ctx Context, provider: &'prov dyn FieldValueProvider) -> Self {
            Self { ctx, provider }
        }

        fn generate(&mut self, expr: &ExprKind) -> Result<ast::Bool<'ctx>, ProofError> {
            self.visit(expr)
        }

        fn get_int_ast(&mut self, expr: &ExprKind) -> Result<ast::Int<'ctx>, ProofError> {
             match expr {
                ExprKind::IntLiteral(v) => Ok(ast::Int::from_i64(self.ctx, *v)),
                ExprKind::UIntLiteral(v) => Ok(ast::Int::from_u64(self.ctx, *v)),
                ExprKind::FieldAccess { field_name } => {
                    match self.provider.get_field_value(field_name)? {
                        FieldValue::Int(i) => Ok(ast::Int::from_i64(self.ctx, i)),
                        FieldValue::UInt(u) => Ok(ast::Int::from_u64(self.ctx, u)),
                        FieldValue::Bool(_) => Err(ProofError::UnsupportedType("Expected int, got bool".into())),
                    }
                },
                ExprKind::ArithmeticOp { left, op, right } => {
                    let left_ast = self.get_int_ast(left)?;
                    let right_ast = self.get_int_ast(right)?;
                    Ok(match op {
                        ArithmeticOp::Add => left_ast + right_ast,
                        ArithmeticOp::Sub => left_ast - right_ast,
                        ArithmeticOp::Mul => left_ast * right_ast,
                        ArithmeticOp::Div => left_ast / right_ast,
                        ArithmeticOp::Rem => left_ast.rem(&right_ast),
                    })
                }
                ExprKind::BitwiseOp { left, op, right } => {
                    let left_ast = self.get_int_ast(left)?;
                    let right_ast = self.get_int_ast(right)?;
                    // Assume 64-bit width for implementation
                    let left_bv = ast::BV::from_int(&left_ast, 64);
                    let right_bv = ast::BV::from_int(&right_ast, 64);
                    let res_bv = match op {
                        BitwiseOp::And => left_bv.bvand(&right_bv),
                        BitwiseOp::Or => left_bv.bvor(&right_bv),
                        BitwiseOp::Xor => left_bv.bvxor(&right_bv),
                        BitwiseOp::Shl => left_bv.bvshl(&right_bv),
                        BitwiseOp::Shr => left_bv.bvlshr(&right_bv),
                    };
                    Ok(res_bv.to_int(false))
                }
                _ => Err(ProofError::UnsupportedType(alloc::format!(
                    "Expected integer expression, got: {:?}",
                    expr
                ))),
            }
        }
    }

    impl<'ctx, 'prov> ExprVisitor for Z3AstGenerator<'ctx, 'prov> {
        type Output = Result<ast::Bool<'ctx>, ProofError>;

        fn visit_int_literal(&mut self, _value: i64) -> Self::Output {
             Err(ProofError::ParseError("Int literal is not bool".into()))
        }
        fn visit_uint_literal(&mut self, _value: u64) -> Self::Output {
             Err(ProofError::ParseError("UInt literal is not bool".into()))
        }
        fn visit_boolean_literal(&mut self, value: bool) -> Self::Output {
            Ok(ast::Bool::from_bool(self.ctx, value))
        }
        fn visit_field_access(&mut self, field_name: &str) -> Self::Output {
             match self.provider.get_field_value(field_name)? {
                FieldValue::Bool(b) => Ok(ast::Bool::from_bool(self.ctx, b)),
                _ => Err(ProofError::UnsupportedType("Expected bool field".into())),
             }
        }

        fn visit_bitwise_op(&mut self, _: &ExprKind, _: BitwiseOp, _: &ExprKind) -> Self::Output {
             Err(ProofError::UnsupportedType("Bitwise op returns int, not bool".into()))
        }
        fn visit_arithmetic_op(&mut self, _: &ExprKind, _: ArithmeticOp, _: &ExprKind) -> Self::Output {
             Err(ProofError::UnsupportedType("Arithmetic op returns int, not bool".into()))
        }

        fn visit_binary_op(&mut self, left: &ExprKind, op: ComparisonOp, right: &ExprKind) -> Self::Output {
            let left_ast = self.get_int_ast(left)?;
            let right_ast = self.get_int_ast(right)?;
            Ok(match op {
                ComparisonOp::Gt => left_ast.gt(&right_ast),
                ComparisonOp::Lt => left_ast.lt(&right_ast),
                ComparisonOp::Eq => left_ast.eq(&right_ast),
                ComparisonOp::Ne => left_ast.eq(&right_ast).not(),
                ComparisonOp::Ge => left_ast.ge(&right_ast),
                ComparisonOp::Le => left_ast.le(&right_ast),
            })
        }

        fn visit_and(&mut self, exprs: &[ExprKind]) -> Self::Output {
             let mut bools = Vec::new();
             for e in exprs { bools.push(self.visit(e)?); }
             let refs: Vec<&_> = bools.iter().collect();
             Ok(ast::Bool::and(&refs))
        }
        fn visit_or(&mut self, exprs: &[ExprKind]) -> Self::Output {
             let mut bools = Vec::new();
             for e in exprs { bools.push(self.visit(e)?); }
             let refs: Vec<&_> = bools.iter().collect();
             Ok(ast::Bool::or(&refs))
        }
        fn visit_not(&mut self, expr: &ExprKind) -> Self::Output {
             Ok(self.visit(expr)?.not())
        }
    }
}

#[cfg(not(feature = "z3-backend"))]
pub mod stub_backend {
    use super::*;

    pub struct StubBackend;

    impl StubBackend {
        pub fn new() -> Result<Self, ProofError> {
            Ok(Self)
        }
    }

    #[async_trait]
    impl SolverBackend for StubBackend {
        async fn verify(
            &self,
            _invariants: &[&str],
            _provider: &dyn FieldValueProvider,
        ) -> Result<VerificationToken, ProofError> {
            Ok(VerificationToken::new())
        }
    }
}
