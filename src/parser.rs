//! Expression Parser for AST Lowering.
//!
//! Converts Rust invariant expression strings (e.g., `"self.balance > 0"`)
//! into an abstract syntax tree that can be used for verification.
//!
//! # Supported Expressions (Phase 1)
//!
//! - Comparison operators: `>`, `<`, `==`, `!=`, `>=`, `<=`
//! - Integer types: `i8`, `i16`, `i32`, `i64`, `u8`, `u16`, `u32`, `u64`
//! - Field access: `self.field_name`
//! - Integer literals
//!
//! # Visitor Pattern
//!
//! The parser uses the Visitor pattern for extensibility. To add support for
//! new expression types:
//!
//! 1. Add a new variant to `ExprKind`
//! 2. Implement the handling in `ExprVisitor::visit_*`
//! 3. Add parsing logic in `ExpressionParser::parse_*`

use crate::ProofError;

/// Represents a parsed expression node.
#[derive(Debug, Clone, PartialEq)]
pub enum ExprKind {
    /// An integer literal value.
    IntLiteral(i64),
    
    /// An unsigned integer literal.
    UIntLiteral(u64),
    
    /// A field access expression (e.g., `self.balance`).
    FieldAccess {
        /// The field name (without `self.` prefix).
        field_name: String,
    },
    
    /// A binary comparison operation.
    BinaryOp {
        left: Box<ExprKind>,
        op: ComparisonOp,
        right: Box<ExprKind>,
    },
    
    /// A logical AND of multiple expressions.
    And(Vec<ExprKind>),
    
    /// A logical OR of multiple expressions.
    Or(Vec<ExprKind>),
    
    /// Logical NOT.
    Not(Box<ExprKind>),
}

/// Comparison operators.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ComparisonOp {
    /// Greater than (`>`)
    Gt,
    /// Less than (`<`)
    Lt,
    /// Equal (`==`)
    Eq,
    /// Not equal (`!=`)
    Ne,
    /// Greater than or equal (`>=`)
    Ge,
    /// Less than or equal (`<=`)
    Le,
}

impl ComparisonOp {
    /// Parses a comparison operator from a string slice.
    pub fn from_str(s: &str) -> Option<Self> {
        match s.trim() {
            ">=" => Some(ComparisonOp::Ge),
            "<=" => Some(ComparisonOp::Le),
            "==" => Some(ComparisonOp::Eq),
            "!=" => Some(ComparisonOp::Ne),
            ">" => Some(ComparisonOp::Gt),
            "<" => Some(ComparisonOp::Lt),
            _ => None,
        }
    }
    
    /// Returns the operator as a string.
    pub fn as_str(&self) -> &'static str {
        match self {
            ComparisonOp::Gt => ">",
            ComparisonOp::Lt => "<",
            ComparisonOp::Eq => "==",
            ComparisonOp::Ne => "!=",
            ComparisonOp::Ge => ">=",
            ComparisonOp::Le => "<=",
        }
    }
}

/// Visitor trait for traversing expression trees.
///
/// Implement this trait to process parsed expressions. The default
/// implementations recursively visit children.
pub trait ExprVisitor {
    /// The output type of visiting an expression.
    type Output;
    
    /// Visit an integer literal.
    fn visit_int_literal(&mut self, value: i64) -> Self::Output;
    
    /// Visit an unsigned integer literal.
    fn visit_uint_literal(&mut self, value: u64) -> Self::Output;
    
    /// Visit a field access.
    fn visit_field_access(&mut self, field_name: &str) -> Self::Output;
    
    /// Visit a binary comparison operation.
    fn visit_binary_op(
        &mut self,
        left: &ExprKind,
        op: ComparisonOp,
        right: &ExprKind,
    ) -> Self::Output;
    
    /// Visit a logical AND.
    fn visit_and(&mut self, exprs: &[ExprKind]) -> Self::Output;
    
    /// Visit a logical OR.
    fn visit_or(&mut self, exprs: &[ExprKind]) -> Self::Output;
    
    /// Visit a logical NOT.
    fn visit_not(&mut self, expr: &ExprKind) -> Self::Output;
    
    /// Dispatch to the appropriate visit method.
    fn visit(&mut self, expr: &ExprKind) -> Self::Output {
        match expr {
            ExprKind::IntLiteral(v) => self.visit_int_literal(*v),
            ExprKind::UIntLiteral(v) => self.visit_uint_literal(*v),
            ExprKind::FieldAccess { field_name } => self.visit_field_access(field_name),
            ExprKind::BinaryOp { left, op, right } => self.visit_binary_op(left, *op, right),
            ExprKind::And(exprs) => self.visit_and(exprs),
            ExprKind::Or(exprs) => self.visit_or(exprs),
            ExprKind::Not(expr) => self.visit_not(expr),
        }
    }
}

/// Parser for invariant expressions.
///
/// Converts string expressions like `"self.balance > 0"` into `ExprKind` AST.
pub struct ExpressionParser;

impl ExpressionParser {
    /// Parses an invariant expression string.
    ///
    /// # Arguments
    ///
    /// * `expr` - The expression string (e.g., `"self.balance > 0"`)
    ///
    /// # Returns
    ///
    /// The parsed expression tree, or a parse error.
    ///
    /// # Supported Syntax
    ///
    /// ```text
    /// expr := comparison | "(" expr ")"
    /// comparison := operand op operand
    /// operand := field_access | integer_literal
    /// field_access := "self." identifier
    /// op := ">" | "<" | "==" | "!=" | ">=" | "<="
    /// ```
    pub fn parse(expr: &str) -> Result<ExprKind, ProofError> {
        let expr = expr.trim();
        
        if expr.is_empty() {
            return Err(ProofError::ParseError("Empty expression".to_string()));
        }
        
        // Try to parse as a comparison expression
        Self::parse_comparison(expr)
    }
    
    /// Parses a comparison expression.
    fn parse_comparison(expr: &str) -> Result<ExprKind, ProofError> {
        // Find the comparison operator (try multi-char first)
        let operators = [">=", "<=", "==", "!=", ">", "<"];
        
        for op_str in operators {
            if let Some(pos) = expr.find(op_str) {
                let left = expr[..pos].trim();
                let right = expr[pos + op_str.len()..].trim();
                
                let op = ComparisonOp::from_str(op_str)
                    .ok_or_else(|| ProofError::ParseError(format!("Unknown operator: {}", op_str)))?;
                
                let left_expr = Self::parse_operand(left)?;
                let right_expr = Self::parse_operand(right)?;
                
                return Ok(ExprKind::BinaryOp {
                    left: Box::new(left_expr),
                    op,
                    right: Box::new(right_expr),
                });
            }
        }
        
        Err(ProofError::ParseError(format!(
            "No comparison operator found in expression: {}", expr
        )))
    }
    
    /// Parses an operand (field access or literal).
    fn parse_operand(operand: &str) -> Result<ExprKind, ProofError> {
        let operand = operand.trim();
        
        // Check for field access (self.field_name)
        if operand.starts_with("self.") {
            let field_name = &operand[5..];
            if field_name.is_empty() {
                return Err(ProofError::ParseError(
                    "Empty field name after 'self.'".to_string()
                ));
            }
            // Validate identifier
            if !Self::is_valid_identifier(field_name) {
                return Err(ProofError::ParseError(format!(
                    "Invalid field name: {}", field_name
                )));
            }
            return Ok(ExprKind::FieldAccess {
                field_name: field_name.to_string(),
            });
        }
        
        // Try to parse as integer literal
        if let Ok(v) = operand.parse::<i64>() {
            return Ok(ExprKind::IntLiteral(v));
        }
        
        // Try to parse as unsigned integer literal (suffixed with 'u')
        if operand.ends_with('u') {
            let num_part = &operand[..operand.len() - 1];
            if let Ok(v) = num_part.parse::<u64>() {
                return Ok(ExprKind::UIntLiteral(v));
            }
        }
        
        Err(ProofError::ParseError(format!(
            "Cannot parse operand: '{}'. Expected 'self.field' or integer literal.", operand
        )))
    }
    
    /// Validates that a string is a valid Rust identifier.
    pub fn is_valid_identifier(s: &str) -> bool {
        if s.is_empty() {
            return false;
        }
        
        let mut chars = s.chars();
        
        // First character must be letter or underscore
        match chars.next() {
            Some(c) if c.is_alphabetic() || c == '_' => {}
            _ => return false,
        }
        
        // Rest must be alphanumeric or underscore
        chars.all(|c| c.is_alphanumeric() || c == '_')
    }
    
    /// Parses multiple invariant expressions and combines them with AND.
    pub fn parse_all(exprs: &[&str]) -> Result<ExprKind, ProofError> {
        if exprs.is_empty() {
            return Err(ProofError::ParseError("No expressions provided".to_string()));
        }
        
        if exprs.len() == 1 {
            return Self::parse(exprs[0]);
        }
        
        let parsed: Result<Vec<_>, _> = exprs.iter().map(|e| Self::parse(e)).collect();
        Ok(ExprKind::And(parsed?))
    }
}

// ============================================================================
// Z3-specific implementations (only when z3-backend feature is enabled)
// ============================================================================

#[cfg(feature = "z3-backend")]
mod z3_impl {
    use super::*;
    use z3::{ast, Context};

    /// Field value provider for Z3 AST generation.
    ///
    /// This trait is implemented by generated code to map field names to Z3 AST nodes.
    pub trait FieldValueProvider<'ctx> {
        /// Returns the Z3 AST for a field, or an error if the field doesn't exist.
        fn get_field_z3(&self, ctx: &'ctx Context, field_name: &str) -> Result<ast::Int<'ctx>, ProofError>;
    }

    /// Visitor that generates Z3 AST from parsed expressions.
    pub struct Z3AstGenerator<'ctx, 'prov, P: FieldValueProvider<'ctx>> {
        ctx: &'ctx Context,
        provider: &'prov P,
    }

    impl<'ctx, 'prov, P: FieldValueProvider<'ctx>> Z3AstGenerator<'ctx, 'prov, P> {
        /// Creates a new Z3 AST generator.
        pub fn new(ctx: &'ctx Context, provider: &'prov P) -> Self {
            Self { ctx, provider }
        }
        
        /// Generates a Z3 boolean assertion from an expression.
        pub fn generate(&mut self, expr: &ExprKind) -> Result<ast::Bool<'ctx>, ProofError> {
            self.visit(expr)
        }
        
        /// Helper to get an integer AST from an expression.
        fn get_int_ast(&mut self, expr: &ExprKind) -> Result<ast::Int<'ctx>, ProofError> {
            match expr {
                ExprKind::IntLiteral(v) => Ok(ast::Int::from_i64(self.ctx, *v)),
                ExprKind::UIntLiteral(v) => Ok(ast::Int::from_u64(self.ctx, *v)),
                ExprKind::FieldAccess { field_name } => self.provider.get_field_z3(self.ctx, field_name),
                _ => Err(ProofError::UnsupportedType(
                    format!("Expected integer expression, got: {:?}", expr)
                )),
            }
        }
    }

    impl<'ctx, 'prov, P: FieldValueProvider<'ctx>> ExprVisitor for Z3AstGenerator<'ctx, 'prov, P> {
        type Output = Result<ast::Bool<'ctx>, ProofError>;
        
        fn visit_int_literal(&mut self, _value: i64) -> Self::Output {
            Err(ProofError::ParseError(
                "Integer literal cannot be used as boolean".to_string()
            ))
        }
        
        fn visit_uint_literal(&mut self, _value: u64) -> Self::Output {
            Err(ProofError::ParseError(
                "Unsigned integer literal cannot be used as boolean".to_string()
            ))
        }
        
        fn visit_field_access(&mut self, _field_name: &str) -> Self::Output {
            Err(ProofError::ParseError(
                "Field access cannot be used as boolean directly".to_string()
            ))
        }
        
        fn visit_binary_op(
            &mut self,
            left: &ExprKind,
            op: ComparisonOp,
            right: &ExprKind,
        ) -> Self::Output {
            let left_ast = self.get_int_ast(left)?;
            let right_ast = self.get_int_ast(right)?;
            
            Ok(match op {
                ComparisonOp::Gt => left_ast.gt(&right_ast),
                ComparisonOp::Lt => left_ast.lt(&right_ast),
                ComparisonOp::Eq => left_ast._eq(&right_ast),
                ComparisonOp::Ne => left_ast._eq(&right_ast).not(),
                ComparisonOp::Ge => left_ast.ge(&right_ast),
                ComparisonOp::Le => left_ast.le(&right_ast),
            })
        }
        
        fn visit_and(&mut self, exprs: &[ExprKind]) -> Self::Output {
            let bools: Result<Vec<_>, _> = exprs.iter().map(|e| self.visit(e)).collect();
            let bools = bools?;
            let refs: Vec<_> = bools.iter().collect();
            Ok(ast::Bool::and(self.ctx, &refs))
        }
        
        fn visit_or(&mut self, exprs: &[ExprKind]) -> Self::Output {
            let bools: Result<Vec<_>, _> = exprs.iter().map(|e| self.visit(e)).collect();
            let bools = bools?;
            let refs: Vec<_> = bools.iter().collect();
            Ok(ast::Bool::or(self.ctx, &refs))
        }
        
        fn visit_not(&mut self, expr: &ExprKind) -> Self::Output {
            let inner = self.visit(expr)?;
            Ok(inner.not())
        }
    }
}

#[cfg(feature = "z3-backend")]
pub use z3_impl::{FieldValueProvider, Z3AstGenerator};

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_greater_than() {
        let result = ExpressionParser::parse("self.balance > 0").unwrap();
        match result {
            ExprKind::BinaryOp { left, op, right } => {
                assert!(matches!(*left, ExprKind::FieldAccess { ref field_name } if field_name == "balance"));
                assert_eq!(op, ComparisonOp::Gt);
                assert!(matches!(*right, ExprKind::IntLiteral(0)));
            }
            _ => panic!("Expected BinaryOp"),
        }
    }

    #[test]
    fn test_parse_less_than_or_equal() {
        let result = ExpressionParser::parse("self.count <= 100").unwrap();
        match result {
            ExprKind::BinaryOp { left, op, right } => {
                assert!(matches!(*left, ExprKind::FieldAccess { ref field_name } if field_name == "count"));
                assert_eq!(op, ComparisonOp::Le);
                assert!(matches!(*right, ExprKind::IntLiteral(100)));
            }
            _ => panic!("Expected BinaryOp"),
        }
    }

    #[test]
    fn test_parse_equality() {
        let result = ExpressionParser::parse("self.id == 42").unwrap();
        match result {
            ExprKind::BinaryOp { left, op, right } => {
                assert!(matches!(*left, ExprKind::FieldAccess { ref field_name } if field_name == "id"));
                assert_eq!(op, ComparisonOp::Eq);
                assert!(matches!(*right, ExprKind::IntLiteral(42)));
            }
            _ => panic!("Expected BinaryOp"),
        }
    }

    #[test]
    fn test_parse_not_equal() {
        let result = ExpressionParser::parse("self.status != 0").unwrap();
        match result {
            ExprKind::BinaryOp { left, op, right } => {
                assert!(matches!(*left, ExprKind::FieldAccess { ref field_name } if field_name == "status"));
                assert_eq!(op, ComparisonOp::Ne);
                assert!(matches!(*right, ExprKind::IntLiteral(0)));
            }
            _ => panic!("Expected BinaryOp"),
        }
    }

    #[test]
    fn test_parse_negative_literal() {
        let result = ExpressionParser::parse("self.temp > -10").unwrap();
        match result {
            ExprKind::BinaryOp { right, .. } => {
                assert!(matches!(*right, ExprKind::IntLiteral(-10)));
            }
            _ => panic!("Expected BinaryOp"),
        }
    }

    #[test]
    fn test_parse_error_no_operator() {
        let result = ExpressionParser::parse("self.balance");
        assert!(matches!(result, Err(ProofError::ParseError(_))));
    }

    #[test]
    fn test_parse_error_empty() {
        let result = ExpressionParser::parse("");
        assert!(matches!(result, Err(ProofError::ParseError(_))));
    }

    #[test]
    fn test_parse_error_invalid_field() {
        let result = ExpressionParser::parse("self. > 0");
        assert!(matches!(result, Err(ProofError::ParseError(_))));
    }

    #[test]
    fn test_parse_all() {
        let exprs = ["self.x > 0", "self.y < 100"];
        let result = ExpressionParser::parse_all(&exprs).unwrap();
        assert!(matches!(result, ExprKind::And(_)));
    }

    #[test]
    fn test_valid_identifier() {
        assert!(ExpressionParser::is_valid_identifier("balance"));
        assert!(ExpressionParser::is_valid_identifier("_private"));
        assert!(ExpressionParser::is_valid_identifier("count123"));
        assert!(!ExpressionParser::is_valid_identifier("123count"));
        assert!(!ExpressionParser::is_valid_identifier(""));
    }

    #[test]
    fn test_comparison_op_from_str() {
        assert_eq!(ComparisonOp::from_str(">"), Some(ComparisonOp::Gt));
        assert_eq!(ComparisonOp::from_str("<"), Some(ComparisonOp::Lt));
        assert_eq!(ComparisonOp::from_str("=="), Some(ComparisonOp::Eq));
        assert_eq!(ComparisonOp::from_str("!="), Some(ComparisonOp::Ne));
        assert_eq!(ComparisonOp::from_str(">="), Some(ComparisonOp::Ge));
        assert_eq!(ComparisonOp::from_str("<="), Some(ComparisonOp::Le));
        assert_eq!(ComparisonOp::from_str("???"), None);
    }
}
