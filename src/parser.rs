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
use alloc::string::{String, ToString};
use alloc::vec::Vec;
use alloc::boxed::Box;
use alloc::format;

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
    
    /// A bitwise operation.
    BitwiseOp {
        left: Box<ExprKind>,
        op: BitwiseOp,
        right: Box<ExprKind>,
    },

    /// An arithmetic operation.
    ArithmeticOp {
        left: Box<ExprKind>,
        op: ArithmeticOp,
        right: Box<ExprKind>,
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

/// Bitwise operators.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BitwiseOp {
    And, // &
    Or,  // |
    Xor, // ^
    Shl, // <<
    Shr, // >>
}

/// Arithmetic operators.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ArithmeticOp {
    Add, // +
    Sub, // -
    Mul, // *
    Div, // /
    Rem, // %
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
    
    /// Visit a bitwise operation.
    fn visit_bitwise_op(
        &mut self,
        left: &ExprKind,
        op: BitwiseOp,
        right: &ExprKind,
    ) -> Self::Output;

    /// Visit an arithmetic operation.
    fn visit_arithmetic_op(
        &mut self,
        left: &ExprKind,
        op: ArithmeticOp,
        right: &ExprKind,
    ) -> Self::Output;

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
            ExprKind::BitwiseOp { left, op, right } => self.visit_bitwise_op(left, *op, right),
            ExprKind::ArithmeticOp { left, op, right } => self.visit_arithmetic_op(left, *op, right),
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
        // This is a simplified precedence parser (precedence climbing could be better but this works for simple invariants)
        // We split by standard operators with precedence:
        // 1. Relational (==, !=, <, >, <=, >=)
        // 2. Bitwise OR (|), XOR (^)
        // 3. Bitwise AND (&)
        // 4. Shift (<<, >>)
        // 5. Add/Sub (+, -)
        // 6. Mul/Div/Rem (*, /, %)
        
        let expr = expr.trim();

        // 1. Relational
        let relational_ops = [">=", "<=", "==", "!=", ">", "<"];
        for op_str in relational_ops {
             if let Some(pos) = find_op_outside_parens(expr, op_str) {
                let left = expr[..pos].trim();
                let right = expr[pos + op_str.len()..].trim();
                let op = ComparisonOp::from_str(op_str).unwrap();
                return Ok(ExprKind::BinaryOp {
                    left: Box::new(Self::parse_comparison(left)?),
                    op,
                    right: Box::new(Self::parse_comparison(right)?),
                });
            }
        }

        // 2. Bitwise OR
        if let Some(pos) = find_op_outside_parens(expr, "|") {
             let left = expr[..pos].trim();
             let right = expr[pos + 1..].trim();
             return Ok(ExprKind::BitwiseOp {
                 left: Box::new(Self::parse_comparison(left)?),
                 op: BitwiseOp::Or,
                 right: Box::new(Self::parse_comparison(right)?),
             });
        }
        
        // 3. Bitwise XOR
        if let Some(pos) = find_op_outside_parens(expr, "^") {
             let left = expr[..pos].trim();
             let right = expr[pos + 1..].trim();
             return Ok(ExprKind::BitwiseOp {
                 left: Box::new(Self::parse_comparison(left)?),
                 op: BitwiseOp::Xor,
                 right: Box::new(Self::parse_comparison(right)?),
             });
        }

        // 4. Bitwise AND
        if let Some(pos) = find_op_outside_parens(expr, "&") {
             let left = expr[..pos].trim();
             let right = expr[pos + 1..].trim();
             return Ok(ExprKind::BitwiseOp {
                 left: Box::new(Self::parse_comparison(left)?),
                 op: BitwiseOp::And,
                 right: Box::new(Self::parse_comparison(right)?),
             });
        }

        // 5. Shift
        let shift_ops = ["<<", ">>"];
        for op_str in shift_ops {
             if let Some(pos) = find_op_outside_parens(expr, op_str) {
                let left = expr[..pos].trim();
                let right = expr[pos + op_str.len()..].trim();
                let op = match op_str { "<<" => BitwiseOp::Shl, ">>" => BitwiseOp::Shr, _ => unreachable!() };
                return Ok(ExprKind::BitwiseOp {
                    left: Box::new(Self::parse_comparison(left)?),
                    op,
                    right: Box::new(Self::parse_comparison(right)?),
                });
            }
        }

        // 6. Add/Sub
        let term_ops = ["+", "-"];
        // loop backwards to support left-associativity if we were scanning, but find_op_outside_parens finds first...
        // Actually for left associativity we want the LAST occurrence. `find_op_outside_parens` finds the first.
        // So `a - b - c` -> `(a) - (b - c)` which is WRONG for sub.
        // We need `find_last_op_outside_parens`.
        
        for op_str in term_ops {
             if let Some(pos) = find_last_op_outside_parens(expr, op_str) {
                let left = expr[..pos].trim();
                let right = expr[pos + op_str.len()..].trim();
                let op = match op_str { "+" => ArithmeticOp::Add, "-" => ArithmeticOp::Sub, _ => unreachable!() };
                return Ok(ExprKind::ArithmeticOp {
                    left: Box::new(Self::parse_comparison(left)?),
                    op,
                    right: Box::new(Self::parse_comparison(right)?),
                });
            }
        }
        
        // 7. Mul/Div/Rem
        let factor_ops = ["*", "/", "%"];
        for op_str in factor_ops {
             if let Some(pos) = find_last_op_outside_parens(expr, op_str) {
                let left = expr[..pos].trim();
                let right = expr[pos + op_str.len()..].trim();
                let op = match op_str { "*" => ArithmeticOp::Mul, "/" => ArithmeticOp::Div, "%" => ArithmeticOp::Rem, _ => unreachable!() };
                return Ok(ExprKind::ArithmeticOp {
                    left: Box::new(Self::parse_comparison(left)?),
                    op,
                    right: Box::new(Self::parse_comparison(right)?),
                });
            }
        }
        
        // Base case: Operand (potentially with parens)
        if expr.starts_with('(') && expr.ends_with(')') {
            // Strip parens
            return Self::parse_comparison(&expr[1..expr.len()-1]);
        }
        
        Self::parse_operand(expr)
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
        
        // Try to parse hex literal
        if operand.starts_with("0x") || operand.starts_with("0X") {
             if let Ok(v) = i64::from_str_radix(&operand[2..], 16) {
                 return Ok(ExprKind::IntLiteral(v));
             }
        }

        // Try to parse as integer literal
        if let Ok(v) = operand.parse::<i64>() {
            return Ok(ExprKind::IntLiteral(v));
        }
        
            Err(ProofError::ParseError(format!(
            "Cannot parse operand: '{}'. Expected 'self.field', hex, or integer literal.", operand
        )))
    }
    
    // Helper to find operator composed of punctuation, ignoring parentheses
fn find_op_outside_parens(expr: &str, op: &str) -> Option<usize> {
    let mut depth = 0;
    let bytes = expr.as_bytes();
    for (i, &b) in bytes.iter().enumerate() {
        match b {
            b'(' => depth += 1,
            b')' => depth -= 1,
            _ => {
                if depth == 0 {
                    if expr[i..].starts_with(op) {
                         return Some(i);
                    }
                }
            }
        }
    }
    None
}

fn find_last_op_outside_parens(expr: &str, op: &str) -> Option<usize> {
    let mut depth = 0;
    let bytes = expr.as_bytes();
    // Scan backwards
    let mut i = bytes.len();
    while i > 0 {
        i -= 1;
        let b = bytes[i];
         match b {
            b')' => depth += 1,
            b'(' => depth -= 1,
            _ => {
                if depth == 0 {
                     // Check if op starts here
                     if expr[i..].starts_with(op) {
                         // Careful with multi-char ops in backwards scan, this logic assumes we invoke it knowing op length
                         return Some(i);
                    }
                }
            }
        }
    }
    None
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
        
        fn visit_bitwise_op(
            &mut self,
            left: &ExprKind,
            op: BitwiseOp,
            right: &ExprKind,
        ) -> Self::Output {
             // Z3 Ints don't support bitwise ops directly in standard SMT-LIB without BV mapping.
             // We will try to map to BV if possible, but the current context is Int.
             // For this iteration, as per instructions: "add the AST nodes... If BitVectors are too complex, stick to Arithmetic".
             // We will ERROR here for now if using Z3 Int backend, or implement basic ones if Z3 supports Int bitwise extensions.
             // Z3 *does* have some Int bitwise support in some contexts but it is non-standard.
             // Let's return error for now to be safe, or implement simple ones.
             
             // However, for the purpose of the task "Map the new ExprKind variants to their corresponding Z3 methods",
             // we should try. "Note: Z3 Ints don't support bitwise ops easily...".
             // We will return UnsupportedType for now as a safe implementation of the "Note".
             Err(ProofError::UnsupportedType("Bitwise operations on Infinite Integers not supported yet. Use BitVectors.".to_string()))
        }

        fn visit_arithmetic_op(
            &mut self,
            left: &ExprKind,
            op: ArithmeticOp,
            right: &ExprKind,
        ) -> Self::Output {
             // Arithmetic ops return Int, but this visitor expects Bool (for the top level?)
             // Wait, generate() returns Bool. But recursive calls might need Int.
             // The structure of Z3AstGenerator assumes `visit` always returns `Result<ast::Bool>`.
             // But for ArithmeticOp, we expect `ast::Int`.
             // We need to refactor Z3AstGenerator to handle different return types or split visitors.
             // For now, failure seems appropriate because strict type system.
             
             // BUT, we can support arithmetic *inside* comparisons.
             // We need `get_int_ast` to recursively call visit? No, `visit` returns Bool.
             // We need a separate `visit_int`?
             
             // Let's modify `get_int_ast` to handle ArithmeticOp recursively.
             Err(ProofError::ParseError("Arithmetic at top-level is not a boolean assertion".to_string()))
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
