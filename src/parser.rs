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
use alloc::boxed::Box;
use alloc::format;
use alloc::string::{String, ToString};
use alloc::vec;
use alloc::vec::Vec;

/// Represents a parsed expression node.
#[derive(Debug, Clone, PartialEq)]
pub enum ExprKind {
    /// An integer literal value.
    IntLiteral(i64),

    /// An unsigned integer literal.
    UIntLiteral(u64),

    /// A boolean literal.
    BooleanLiteral(bool),

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
    #[allow(clippy::should_implement_trait)]
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

    /// Visit a boolean literal.
    fn visit_boolean_literal(&mut self, value: bool) -> Self::Output;

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
            ExprKind::BooleanLiteral(v) => self.visit_boolean_literal(*v),
            ExprKind::FieldAccess { field_name } => self.visit_field_access(field_name),
            ExprKind::BitwiseOp { left, op, right } => self.visit_bitwise_op(left, *op, right),
            ExprKind::ArithmeticOp { left, op, right } => {
                self.visit_arithmetic_op(left, *op, right)
            }
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
        let result = Self::parse_comparison(expr)?;

        // Validate that the result is a comparison/logical expression, not just an operand
        // This ensures invariants like "self.balance" (missing operator) are rejected
        match &result {
            ExprKind::BinaryOp { .. }
            | ExprKind::And(_)
            | ExprKind::Or(_)
            | ExprKind::Not(_)
            | ExprKind::BooleanLiteral(_) => Ok(result),
            ExprKind::FieldAccess { .. } | ExprKind::IntLiteral(_) | ExprKind::UIntLiteral(_) => {
                Err(ProofError::ParseError(
                    "Expression must be a comparison (e.g., 'self.x > 0'), not just a value"
                        .to_string(),
                ))
            }

            // Allow arithmetic/bitwise as they may be part of larger expressions
            // Update: We now allow arithmetic/bitwise ops at the root (for flexibility),
            // though they might not be valid boolean assertions without comparison.
            // But typical usage in invariants might be `flags & 1` (implicitly boolean in C, but Rust is strict).
            // However, the prompt specifically says "accept ArithmeticOp recursively" and "The parser currently rejects ArithmeticOp at the root".
            // So we allow it.
            ExprKind::ArithmeticOp { .. } | ExprKind::BitwiseOp { .. } => Ok(result),
        }
    }

    /// Parses a comparison expression using precedence climbing.
    fn parse_comparison(expr: &str) -> Result<ExprKind, ProofError> {
        let tokens = Tokenizer::tokenize(expr)?;
        let (expr, _) = Self::parse_expression_climbing(&tokens, 0, 0)?;
        Ok(expr)
    }

    /// Precedence climbing parser.
    fn parse_expression_climbing(
        tokens: &[Token],
        min_precedence: u8,
        depth: usize,
    ) -> Result<(ExprKind, usize), ProofError> {
        if depth > 50 {
            return Err(ProofError::ParseError(
                "Maximum recursion depth exceeded (limit 50)".to_string(),
            ));
        }

        if tokens.is_empty() {
            return Err(ProofError::ParseError(
                "Unexpected end of expression".to_string(),
            ));
        }

        // 1. Parse LHS (atom)
        let (mut lhs, mut idx) = Self::parse_atom(tokens, depth + 1)?;

        // 2. Loop while next token is operator with precedence >= min_precedence
        while idx < tokens.len() {
            let token = &tokens[idx];

            if let Token::Op(op_str) = token {
                let precedence = Self::get_precedence(op_str);
                if precedence < min_precedence {
                    break;
                }

                let op_str = op_str.clone();
                idx += 1; // consume operator

                // 3. Parse RHS with higher precedence
                // Right-associativity -> min_precedence = precedence
                // Left-associativity -> min_precedence = precedence + 1
                // We'll use left-associativity for most standard ops
                let next_min_precedence = precedence + 1;

                let (rhs, rhs_consumed) = Self::parse_expression_climbing(
                    &tokens[idx..],
                    next_min_precedence,
                    depth + 1,
                )?;
                idx += rhs_consumed;

                lhs = Self::combine_expr(lhs, &op_str, rhs)?;
            } else {
                break;
            }
        }

        Ok((lhs, idx))
    }

    fn parse_atom(tokens: &[Token], depth: usize) -> Result<(ExprKind, usize), ProofError> {
        if tokens.is_empty() {
            return Err(ProofError::ParseError(
                "Unexpected end of expression".to_string(),
            ));
        }

        match &tokens[0] {
            Token::LParen => {
                let (expr, consumed) = Self::parse_expression_climbing(&tokens[1..], 0, depth + 1)?;
                if tokens.len() <= 1 + consumed || tokens[1 + consumed] != Token::RParen {
                    return Err(ProofError::ParseError("Mismatched parentheses".to_string()));
                }
                Ok((expr, 1 + consumed + 1))
            }
            Token::Literal(n) => Ok((ExprKind::IntLiteral(*n), 1)),
            Token::Bool(b) => Ok((ExprKind::BooleanLiteral(*b), 1)),
            Token::Field(name) => {
                if let Some(field_part) = name.strip_prefix("self.") {
                    let field_part = &field_part;
                    if field_part.is_empty() || !Self::is_valid_identifier(field_part) {
                        return Err(ProofError::ParseError(format!(
                            "Invalid field identifier in '{}'",
                            name
                        )));
                    }
                    Ok((
                        ExprKind::FieldAccess {
                            field_name: field_part.to_string(),
                        },
                        1,
                    ))
                } else {
                    Err(ProofError::ParseError(format!(
                        "Invalid operand '{}'. Expected 'self.field' or literal.",
                        name
                    )))
                }
            }
            _ => Err(ProofError::ParseError(format!(
                "Unexpected token: {:?}",
                tokens[0]
            ))),
        }
    }

    fn get_precedence(op: &str) -> u8 {
        match op {
            "||" => 1,
            "&&" => 2,
            "==" | "!=" | "<" | ">" | "<=" | ">=" => 3,
            "+" | "-" | "|" | "^" => 4,
            "*" | "/" | "%" | "&" | "<<" | ">>" => 5,
            _ => 0,
        }
    }

    fn combine_expr(lhs: ExprKind, op: &str, rhs: ExprKind) -> Result<ExprKind, ProofError> {
        // Relational
        if let Some(cmp) = ComparisonOp::from_str(op) {
            return Ok(ExprKind::BinaryOp {
                left: Box::new(lhs),
                op: cmp,
                right: Box::new(rhs),
            });
        }

        // Arithmetic
        let arith = match op {
            "+" => Some(ArithmeticOp::Add),
            "-" => Some(ArithmeticOp::Sub),
            "*" => Some(ArithmeticOp::Mul),
            "/" => Some(ArithmeticOp::Div),
            "%" => Some(ArithmeticOp::Rem),
            _ => None,
        };
        if let Some(aop) = arith {
            return Ok(ExprKind::ArithmeticOp {
                left: Box::new(lhs),
                op: aop,
                right: Box::new(rhs),
            });
        }

        // Bitwise
        let bit = match op {
            "&" => Some(BitwiseOp::And),
            "|" => Some(BitwiseOp::Or),
            "^" => Some(BitwiseOp::Xor),
            "<<" => Some(BitwiseOp::Shl),
            ">>" => Some(BitwiseOp::Shr),
            _ => None,
        };
        if let Some(bop) = bit {
            return Ok(ExprKind::BitwiseOp {
                left: Box::new(lhs),
                op: bop,
                right: Box::new(rhs),
            });
        }

        // Logical
        match op {
            "&&" => Ok(ExprKind::And(vec![lhs, rhs])), // Simplified binary tree for And
            "||" => Ok(ExprKind::Or(vec![lhs, rhs])),
            _ => Err(ProofError::ParseError(format!("Unknown operator: {}", op))),
        }
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
            return Err(ProofError::ParseError(
                "No expressions provided".to_string(),
            ));
        }

        if exprs.len() == 1 {
            return Self::parse(exprs[0]);
        }

        // Fix: Use generic iteration to allow collect into Result<Vec<_>, _>
        let parsed: Result<Vec<_>, _> = exprs.iter().map(|e| Self::parse(e)).collect();
        Ok(ExprKind::And(parsed?))
    }
}

// ============================================================================
// Verification Interfaces (Used by Macro)
// ============================================================================

use crate::ast;

/// Field value provider for Z3 AST generation.
///
/// This trait is implemented by generated code to map field names to Z3 AST nodes.
pub trait FieldValueProvider {
    /// Returns the Z3 AST for a field, or an error if the field doesn't exist.
    fn get_field_z3(&self, field_name: &str) -> Result<ast::Int, ProofError>;
}

// ============================================================================
// Z3-specific implementations (only when z3-backend feature is enabled)
// ============================================================================

#[derive(Debug, PartialEq, Clone)]
enum Token {
    Literal(i64),
    Bool(bool),
    Field(String),
    Op(String),
    LParen,
    RParen,
}

struct Tokenizer;

impl Tokenizer {
    fn tokenize(input: &str) -> Result<Vec<Token>, ProofError> {
        let mut tokens = Vec::new();
        let mut chars = input.chars().peekable();

        while let Some(&c) = chars.peek() {
            if c.is_whitespace() {
                chars.next();
            } else if c == '(' {
                tokens.push(Token::LParen);
                chars.next();
            } else if c == ')' {
                tokens.push(Token::RParen);
                chars.next();
            } else if c.is_ascii_digit() || c == '-' {
                if c == '-' {
                    let mut temp_iter = chars.clone();
                    temp_iter.next();
                    match temp_iter.peek() {
                        Some(&next_c) if next_c.is_ascii_digit() => {} // is number
                        _ => {
                            tokens.push(Token::Op("-".to_string()));
                            chars.next();
                            continue;
                        }
                    }
                }

                let mut num_str = String::new();
                if c == '-' {
                    num_str.push(c);
                    chars.next();
                }

                if chars.peek() == Some(&'0') {
                    let mut lookahead = chars.clone();
                    lookahead.next();
                    #[allow(clippy::collapsible_if)]
                    if let Some(&x) = lookahead.peek() {
                        if x == 'x' || x == 'X' {
                            chars.next();
                            chars.next(); // 0x
                            let mut hex_val = String::new();
                            while let Some(&hc) = chars.peek() {
                                if hc.is_ascii_hexdigit() {
                                    hex_val.push(hc);
                                    chars.next();
                                } else {
                                    break;
                                }
                            }
                            let val = i64::from_str_radix(&hex_val, 16)?;
                            tokens.push(Token::Literal(val));
                            continue;
                        }
                    }
                }

                while let Some(&d) = chars.peek() {
                    if d.is_ascii_digit() {
                        num_str.push(d);
                        chars.next();
                    } else {
                        break;
                    }
                }
                let val = num_str.parse::<i64>()?;
                tokens.push(Token::Literal(val));
            } else if Self::is_start_of_identifier(c) {
                let mut ident = String::new();
                while let Some(&ic) = chars.peek() {
                    if ic.is_alphanumeric() || ic == '_' || ic == '.' {
                        ident.push(ic);
                        chars.next();
                    } else {
                        break;
                    }
                }
                match ident.as_str() {
                    "true" => tokens.push(Token::Bool(true)),
                    "false" => tokens.push(Token::Bool(false)),
                    _ => tokens.push(Token::Field(ident)),
                }
            } else {
                let mut op = String::new();
                op.push(chars.next().unwrap());

                if let Some(&nc) = chars.peek() {
                    let two_char = format!("{}{}", op, nc);
                    if ["==", "!=", ">=", "<=", "<<", ">>", "||", "&&"].contains(&two_char.as_str())
                    {
                        op = two_char;
                        chars.next();
                    }
                }
                tokens.push(Token::Op(op));
            }
        }
        Ok(tokens)
    }

    fn is_start_of_identifier(c: char) -> bool {
        c.is_alphabetic() || c == '_'
    }
}

#[cfg(feature = "z3-backend")]
mod z3_impl {
    use super::*;
    // Use types from crate root which are aliases to z3 types when backend is on
    // Use types from crate root which are aliases to z3 types when backend is on
    use crate::Context;
    use crate::ast;

    /// Visitor that generates Z3 AST from parsed expressions.
    pub struct Z3AstGenerator<'prov, 'ctx, P: FieldValueProvider + ?Sized> {
        provider: &'prov P,
        ctx: &'ctx Context,
    }

    impl<'prov, 'ctx, P: FieldValueProvider + ?Sized> Z3AstGenerator<'prov, 'ctx, P> {
        /// Creates a new Z3 AST generator.
        pub fn new(ctx: &'ctx Context, provider: &'prov P) -> Self {
            Self { provider, ctx }
        }

        /// Generates a Z3 boolean assertion from an expression.
        pub fn generate(&mut self, expr: &ExprKind) -> Result<ast::Bool, ProofError> {
            self.visit(expr)
        }

        /// Helper to get an integer AST from an expression.
        fn get_int_ast(&mut self, expr: &ExprKind) -> Result<ast::Int, ProofError> {
            match expr {
                ExprKind::IntLiteral(v) => Ok(ast::Int::from_i64(*v)),
                ExprKind::UIntLiteral(v) => Ok(ast::Int::from_u64(*v)),
                ExprKind::FieldAccess { field_name } => self.provider.get_field_z3(field_name),
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
                _ => Err(ProofError::UnsupportedType(format!(
                    "Expected integer expression, got: {:?}",
                    expr
                ))),
            }
        }
    }

    impl<'prov, 'ctx, P: FieldValueProvider + ?Sized> ExprVisitor for Z3AstGenerator<'prov, 'ctx, P> {
        type Output = Result<ast::Bool, ProofError>;

        fn visit_int_literal(&mut self, _value: i64) -> Self::Output {
            Err(ProofError::ParseError(
                "Integer literal cannot be used as boolean".to_string(),
            ))
        }

        fn visit_uint_literal(&mut self, _value: u64) -> Self::Output {
            Err(ProofError::ParseError(
                "Unsigned integer literal cannot be used as boolean".to_string(),
            ))
        }

        fn visit_boolean_literal(&mut self, value: bool) -> Self::Output {
            Ok(ast::Bool::from_bool(self.ctx, value))
        }

        fn visit_field_access(&mut self, _field_name: &str) -> Self::Output {
            Err(ProofError::ParseError(
                "Field access cannot be used as boolean directly".to_string(),
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
                ComparisonOp::Eq => left_ast.eq(&right_ast),
                ComparisonOp::Ne => left_ast.eq(&right_ast).not(),
                ComparisonOp::Ge => left_ast.ge(&right_ast),
                ComparisonOp::Le => left_ast.le(&right_ast),
            })
        }

        fn visit_bitwise_op(
            &mut self,
            _left: &ExprKind,
            _op: BitwiseOp,
            _right: &ExprKind,
        ) -> Self::Output {
            // Z3 Int bitwise ops not supported in this binding context easily
            Err(ProofError::UnsupportedType(
                "Bitwise operations on Infinite Integers not supported yet.".to_string(),
            ))
        }

        fn visit_arithmetic_op(
            &mut self,
            _left: &ExprKind,
            _op: ArithmeticOp,
            _right: &ExprKind,
        ) -> Self::Output {
            Err(ProofError::ParseError(
                "Arithmetic at top-level is not a boolean assertion".to_string(),
            ))
        }

        fn visit_and(&mut self, exprs: &[ExprKind]) -> Self::Output {
            let bools: Result<Vec<_>, _> = exprs.iter().map(|e| self.visit(e)).collect();
            let bools = bools?;
            let refs: Vec<_> = bools.iter().collect();
            Ok(ast::Bool::and(&refs))
        }

        fn visit_or(&mut self, exprs: &[ExprKind]) -> Self::Output {
            let bools: Result<Vec<_>, _> = exprs.iter().map(|e| self.visit(e)).collect();
            let bools = bools?;
            let refs: Vec<_> = bools.iter().collect();
            Ok(ast::Bool::or(&refs))
        }

        fn visit_not(&mut self, expr: &ExprKind) -> Self::Output {
            let inner = self.visit(expr)?;
            Ok(inner.not())
        }
    }
}

#[cfg(feature = "z3-backend")]
pub use z3_impl::Z3AstGenerator;

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
                assert!(
                    matches!(*left, ExprKind::FieldAccess { ref field_name } if field_name == "balance")
                );
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
                assert!(
                    matches!(*left, ExprKind::FieldAccess { ref field_name } if field_name == "count")
                );
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
                assert!(
                    matches!(*left, ExprKind::FieldAccess { ref field_name } if field_name == "id")
                );
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
                assert!(
                    matches!(*left, ExprKind::FieldAccess { ref field_name } if field_name == "status")
                );
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

    #[test]
    fn test_precedence_arithmetic() {
        // self.x + 2 > 5
        // Arithmetic (prec 4) should bind tighter than Comparison (prec 3)
        let result = ExpressionParser::parse("self.x + 2 > 5").unwrap();
        match result {
            ExprKind::BinaryOp { left, op, right } => {
                assert_eq!(op, ComparisonOp::Gt);
                assert!(matches!(*right, ExprKind::IntLiteral(5)));

                match *left {
                    ExprKind::ArithmeticOp {
                        left: _l2,
                        op: op2,
                        right: _r2,
                    } => {
                        assert_eq!(op2, ArithmeticOp::Add);
                    }
                    _ => panic!("Expected ArithmeticOp on LHS"),
                }
            }
            _ => panic!("Expected BinaryOp"),
        }
    }

    #[test]
    fn test_parse_boolean_literals() {
        let result = ExpressionParser::parse("true").unwrap();
        assert!(matches!(result, ExprKind::BooleanLiteral(true)));

        let result = ExpressionParser::parse("false").unwrap();
        assert!(matches!(result, ExprKind::BooleanLiteral(false)));
    }

    #[test]
    fn test_complex_grouping_precedence() {
        // (self.a == 1 || self.b == 2) && self.c == 3
        let result =
            ExpressionParser::parse("(self.a == 1 || self.b == 2) && self.c == 3").unwrap();
        match result {
            ExprKind::And(exprs) => {
                assert_eq!(exprs.len(), 2);
                match &exprs[0] {
                    ExprKind::Or(_) => {} // Correct (self.a || self.b)
                    _ => panic!("Expected Or on LHS, got {:?}", exprs[0]),
                }
                match &exprs[1] {
                    ExprKind::BinaryOp { .. } => {} // self.c == 3
                    _ => panic!("Expected BinaryOp on RHS"),
                }
            }
            _ => panic!("Expected And as root, got {:?}", result),
        }
    }
}

// ============================================================================
// Tests
// ============================================================================
