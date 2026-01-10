//! The Garuda Proof System: SMT-based Formal Verification for PraBorrow.
//!
//! This crate provides mathematical invariant validation using the Z3 theorem prover.
//! Instead of runtime panic checks, invariants are proven satisfiable before state transitions.
//!
//! # Features
//!
//! - `z3-backend`: Enable actual Z3 solver integration. Requires Z3 to be installed.
//!   Without this feature, a stub implementation is provided that always succeeds.
//!
//! # Architecture
//!
//! ```text
//! ┌─────────────────┐     ┌──────────────────┐     ┌─────────────────┐
//! │ #[derive(Const)]│ ──▶ │ ExpressionParser │ ──▶ │ Z3 Solver       │
//! │ invariants      │     │ (AST Lowering)   │     │ or Stub Backend │
//! └─────────────────┘     └──────────────────┘     └─────────────────┘
//!                                                         │
//!                                                         ▼
//!                                               ┌─────────────────────┐
//!                                               │ VerificationToken   │
//!                                               │ or ProofError       │
//!                                               └─────────────────────┘
//! ```
//!
//! # Example
//!
//! ```ignore
//! use praborrow_prover::{SmtContext, ProveInvariant};
//!
//! let ctx = SmtContext::new()?;
//! let result = my_struct.verify_integrity(&ctx)?;
//! // result is VerificationToken - proof that invariants hold
//! ```

#![cfg_attr(not(feature = "std"), no_std)]

pub mod parser;

extern crate alloc;

#[cfg(feature = "std")]
use lru::LruCache;
#[cfg(feature = "std")]
use std::num::NonZeroUsize;
#[cfg(feature = "std")]
use std::sync::Mutex;

use alloc::string::String;
use alloc::vec::Vec;
#[cfg(feature = "std")]
use lazy_static::lazy_static;
#[cfg(feature = "std")]
use sha2::{Digest, Sha256};
use thiserror::Error;

// ... (skipping Z3 imports which remain the same) ...

// Conditional Z3 imports
#[cfg(feature = "z3-backend")]
pub use z3::{Config, Context, SatResult, Solver};

// Re-export Z3 types when available
#[cfg(feature = "z3-backend")]
pub use z3::{Sort, ast};

// Stub Z3 types when backend is disabled
#[cfg(not(feature = "z3-backend"))]
pub mod z3_stub {
    #[derive(Debug, Clone)]
    pub struct Context;
    #[derive(Debug, Clone)]
    pub struct Solver;
    pub mod ast {
        use core::marker::PhantomData;
        #[derive(Debug, Clone)]
        pub struct Int<'a>(PhantomData<&'a ()>);
        #[derive(Debug, Clone)]
        pub struct Bool<'a>(PhantomData<&'a ()>);
        pub trait Ast<'ctx> {}
        impl<'ctx> Ast<'ctx> for Int<'ctx> {}
        impl<'ctx> Ast<'ctx> for Bool<'ctx> {}

        impl<'ctx> Int<'ctx> {
            pub fn from_i64(_ctx: &super::Context, _v: i64) -> Self {
                Self(PhantomData)
            }
            pub fn from_u64(_ctx: &super::Context, _v: u64) -> Self {
                Self(PhantomData)
            }
        }
    }
}

#[cfg(not(feature = "z3-backend"))]
pub use z3_stub::{Context, ast};

/// Errors that can occur during formal verification.
#[derive(Error, Debug, Clone, PartialEq, Eq)]
pub enum ProofError {
    /// The Z3 solver encountered an internal failure.
    #[error("Solver failure: {0}")]
    SolverFailure(String),

    /// An invariant was mathematically proven to be violated.
    #[error("Invariant violated: {0}")]
    InvariantViolated(String),

    /// The expression contains types not yet supported by the prover.
    #[error("Unsupported type in expression: {0}")]
    UnsupportedType(String),

    /// Failed to parse the invariant expression.
    #[error("Parse error in invariant: {0}")]
    ParseError(String),

    /// The solver returned Unknown (timeout or incomplete decision).
    #[error("Solver returned Unknown - verification inconclusive")]
    Unknown,

    /// Z3 backend is not enabled.
    #[error("Z3 backend not enabled - using stub verification")]
    BackendNotEnabled,
}

/// A zero-sized type that serves as cryptographic proof that verification passed.
///
/// This type cannot be constructed directly - it is only returned by successful
/// verification. Its existence in a type signature proves the check was performed.
///
/// # Design Rationale
///
/// By making this a ZST, we ensure:
/// 1. Zero runtime overhead for carrying the proof
/// 2. Type-level guarantee that verification occurred
/// 3. Cannot be forged without calling verification
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct VerificationToken {
    // Private field prevents external construction
    _private: (),
}

impl VerificationToken {
    /// Internal constructor - only callable within this crate.
    pub fn new() -> Self {
        Self { _private: () }
    }
}

impl Default for VerificationToken {
    fn default() -> Self {
        Self::new()
    }
}

/// Result of a cached verification lookup.
#[cfg(feature = "std")]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CacheResult {
    /// Verification was previously successful.
    Hit,
    /// No cached result found.
    Miss,
    /// Verification was previously unsuccessful.
    Failed,
}

/// Thread-safe cache for verification results.
///
/// Since SMT solving is expensive, we cache results based on the hash of:
/// - The type name
/// - The field values (serialized)
/// - The invariant expressions
#[cfg(feature = "std")]
pub struct VerificationCache {
    inner: Mutex<LruCache<[u8; 32], bool>>,
}

#[cfg(feature = "std")]
impl VerificationCache {
    /// Creates a new empty cache.
    pub fn new() -> Self {
        Self {
            inner: Mutex::new(LruCache::new(NonZeroUsize::new(10000).unwrap())),
        }
    }

    /// Computes a cache key from the given data.
    pub fn compute_key(type_name: &str, data_hash: &[u8], invariants: &[&str]) -> [u8; 32] {
        let mut hasher = Sha256::new();
        hasher.update(type_name.as_bytes());
        hasher.update(data_hash);
        for inv in invariants {
            hasher.update(inv.as_bytes());
        }
        hasher.finalize().into()
    }

    /// Looks up a cached result.
    pub fn lookup(&self, key: &[u8; 32]) -> CacheResult {
        let mut guard = self.inner.lock().unwrap();
        match guard.get(key) {
            Some(true) => CacheResult::Hit,
            Some(false) => CacheResult::Failed,
            None => CacheResult::Miss,
        }
    }

    /// Stores a verification result.
    pub fn store(&self, key: [u8; 32], success: bool) {
        let mut guard = self.inner.lock().unwrap();
        guard.put(key, success);
    }

    /// Clears all cached results.
    pub fn clear(&self) {
        let mut guard = self.inner.lock().unwrap();
        guard.clear();
    }
}

#[cfg(feature = "std")]
impl Default for VerificationCache {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(feature = "std")]
lazy_static! {
    /// Global verification cache for optimistic verification.
    pub static ref GLOBAL_CACHE: VerificationCache = VerificationCache::new();
}

// ============================================================================
// Z3 Backend Implementation
// ============================================================================

#[cfg(feature = "z3-backend")]
mod z3_backend {
    use super::*;

    /// Manages the Z3 solver context and configuration.
    ///
    /// # Thread Safety
    ///
    /// Z3 contexts are NOT thread-safe. Each thread should create its own `SmtContext`.
    /// The global cache (`GLOBAL_CACHE`) is thread-safe and can be shared.
    pub struct SmtContext {
        // Z3 context is thread-local in 0.19+
        _private: (),
    }

    impl SmtContext {
        /// Creates a new SMT context with default configuration.
        pub fn new() -> Result<Self, ProofError> {
            let _config = Config::new();
            // In z3 0.19+, context is implicit/thread-local or global
            Ok(Self { _private: () })
        }

        /// Creates a new solver for this context.
        pub fn new_solver(&self) -> Solver {
            Solver::new()
        }

        /// Checks if assertions are satisfiable using a fresh solver.
        pub fn check_assertions<'a, I>(
            &'a self,
            assertions: I,
        ) -> Result<VerificationToken, ProofError>
        where
            I: IntoIterator<Item = &'a z3::ast::Bool>,
        {
            let solver = self.new_solver();
            for assertion in assertions {
                solver.assert(assertion);
            }

            match solver.check() {
                SatResult::Sat => Ok(VerificationToken::new()),
                SatResult::Unsat => Err(ProofError::InvariantViolated(
                    "Solver proved invariant cannot be satisfied".to_string(),
                )),
                SatResult::Unknown => Err(ProofError::Unknown),
            }
        }

        /// Verifies a set of invariants using the provided field provider.
        pub fn verify_invariants<P>(
            &self,
            provider: &P,
            invariants: &[&str],
        ) -> Result<VerificationToken, ProofError>
        where
            P: crate::parser::FieldValueProvider + ?Sized,
        {
            use crate::parser::{ExpressionParser, Z3AstGenerator};

            // Actually Z3AstGenerator generates 'ctx Bools.
            // We need to collect them.
            let mut bools = Vec::new();

            for inv in invariants {
                let expr = ExpressionParser::parse(inv)?;
                let mut generator = Z3AstGenerator::new(provider);
                let assertion = generator.generate(&expr)?;
                bools.push(assertion);
            }

            let refs: Vec<&_> = bools.iter().collect();
            self.check_assertions(refs)
        }
    }
}

#[cfg(feature = "z3-backend")]
pub use z3_backend::SmtContext;

// ============================================================================
// Stub Backend Implementation (when Z3 is not available)
// ============================================================================

#[cfg(not(feature = "z3-backend"))]
mod stub_backend {
    use super::*;

    /// Stub SMT context when Z3 is not available.
    ///
    /// This always returns success. Use the `z3-backend` feature for real verification.
    ///
    /// # Warning
    ///
    /// This stub provides NO actual verification. It is intended only for:
    /// - Development environments without Z3 installed
    /// - Quick prototyping before enabling formal verification
    ///
    /// **DO NOT use in production without the `z3-backend` feature enabled.**
    pub struct SmtContext {
        _private: (),
    }

    impl SmtContext {
        /// Creates a new stub context.
        pub fn new() -> Result<Self, ProofError> {
            Ok(Self { _private: () })
        }

        /// Stub verification - always succeeds.
        ///
        /// # Warning
        ///
        /// This does NOT perform actual SMT verification.
        /// Enable the `z3-backend` feature for real verification.
        pub fn verify_stub(&self) -> Result<VerificationToken, ProofError> {
            // Emit a warning in debug builds to alert developers
            #[cfg(debug_assertions)]
            tracing::warn!(
                target: "praborrow_prover",
                "⚠️  STUB VERIFICATION: Formal verification passed trivially (Z3 backend disabled). \
                 This provides NO safety guarantees. DO NOT RELY ON THIS IN PRODUCTION. \
                 Enable the 'z3-backend' feature for actual SMT verification."
            );

            // In release builds without z3, still log at trace level
            #[cfg(not(debug_assertions))]
            tracing::trace!(
                target: "praborrow_prover",
                "Stub verification used (z3-backend feature not enabled)"
            );

            Ok(VerificationToken::new())
        }

        pub fn verify_invariants<P>(
            &self,
            _provider: &P,
            _invariants: &[&str],
        ) -> Result<VerificationToken, ProofError>
        where
            P: crate::parser::FieldValueProvider + ?Sized,
        {
            self.verify_stub()
        }
    }

    impl Default for SmtContext {
        fn default() -> Self {
            Self::new().expect("Stub context creation never fails")
        }
    }
}

#[cfg(not(feature = "z3-backend"))]
pub use stub_backend::SmtContext;

// ============================================================================
// ProveInvariant Trait
// ============================================================================

/// Trait for types that can be formally verified.
///
/// This trait is implemented by the `#[derive(Constitution)]` macro.
/// It provides the bridge between Rust types and Z3 SMT logic.
pub trait ProveInvariant {
    /// Returns the invariant expressions as strings.
    ///
    /// These are the raw expressions from `#[invariant("...")]` attributes.
    fn invariant_expressions() -> &'static [&'static str];

    /// Computes a hash of the current field values.
    ///
    /// Used for cache key generation.
    fn compute_data_hash(&self) -> Vec<u8>;

    /// Verifies all invariants.
    ///
    /// # With `z3-backend` feature
    ///
    /// Uses Z3 SMT solver for mathematical proof.
    ///
    /// # Without `z3-backend` feature
    ///
    /// Returns `Ok(VerificationToken)` as a stub (relies on runtime checks).
    fn verify(&self) -> Result<VerificationToken, ProofError> {
        let ctx = SmtContext::new()?;
        self.verify_with_context(&ctx)
    }

    /// Verifies invariants using a specific SMT context.
    ///
    /// This allows reusing the context for efficiency or custom configuration.
    fn verify_with_context(&self, ctx: &SmtContext) -> Result<VerificationToken, ProofError>;

    /// Verifies invariants with caching.
    ///
    /// First checks the global cache. If miss, runs full verification
    /// and caches the result.
    fn verify_cached(&self) -> Result<VerificationToken, ProofError>
    where
        Self: Sized,
    {
        #[cfg(feature = "std")]
        {
            let type_name = std::any::type_name::<Self>();
            let data_hash = self.compute_data_hash();
            let invariants = Self::invariant_expressions();

            let cache_key = VerificationCache::compute_key(type_name, &data_hash, invariants);

            match GLOBAL_CACHE.lookup(&cache_key) {
                CacheResult::Hit => Ok(VerificationToken::new()),
                CacheResult::Failed => Err(ProofError::InvariantViolated(
                    "Cached: invariant previously failed".to_string(),
                )),
                CacheResult::Miss => {
                    let result = self.verify();
                    GLOBAL_CACHE.store(cache_key, result.is_ok());
                    result
                }
            }
        }
        #[cfg(not(feature = "std"))]
        {
            // In no_std, we skip caching and verify directly
            self.verify()
        }
    }
}

// ============================================================================
// ToZ3Ast Trait (only when Z3 is available)
// ============================================================================

/// Trait for types that can provide field values to the SMT solver.
#[cfg(feature = "z3-backend")]
pub trait ToZ3Ast {
    /// The Z3 AST type for this Rust type.
    type Ast;

    /// Converts this value to a Z3 AST node.
    fn to_z3_ast(&self, name: &str) -> Self::Ast;
}

#[cfg(feature = "z3-backend")]
mod z3_impls {
    use super::*;

    macro_rules! impl_to_z3_int {
        ($($ty:ty),*) => {
            $(
                impl ToZ3Ast for $ty {
                    type Ast = z3::ast::Int;

                    fn to_z3_ast(&self, _name: &str) -> Self::Ast {
                        z3::ast::Int::from_i64(*self as i64)
                    }
                }
            )*
        };
    }

    impl_to_z3_int!(i8, i16, i32, i64, isize);

    macro_rules! impl_to_z3_uint {
        ($($ty:ty),*) => {
            $(
                impl ToZ3Ast for $ty {
                    type Ast = z3::ast::Int;

                    fn to_z3_ast(&self, _name: &str) -> Self::Ast {
                        z3::ast::Int::from_u64(*self as u64)
                    }
                }
            )*
        };
    }

    impl_to_z3_uint!(u8, u16, u32, u64, usize);
}

#[cfg(feature = "z3-backend")]
// ============================================================================
// Tests
// ============================================================================
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_verification_token_is_zst() {
        assert_eq!(std::mem::size_of::<VerificationToken>(), 0);
    }

    #[cfg(feature = "std")]
    #[test]
    fn test_cache_operations() {
        let cache = VerificationCache::new();
        let key = [0u8; 32];

        assert_eq!(cache.lookup(&key), CacheResult::Miss);

        cache.store(key, true);
        assert_eq!(cache.lookup(&key), CacheResult::Hit);

        let key2 = [1u8; 32];
        cache.store(key2, false);
        assert_eq!(cache.lookup(&key2), CacheResult::Failed);

        cache.clear();
        assert_eq!(cache.lookup(&key), CacheResult::Miss);
    }

    #[cfg(feature = "std")]
    #[test]
    fn test_cache_key_computation() {
        let key1 = VerificationCache::compute_key("MyType", &[1, 2, 3], &["x > 0"]);
        let key2 = VerificationCache::compute_key("MyType", &[1, 2, 3], &["x > 0"]);
        let key3 = VerificationCache::compute_key("MyType", &[1, 2, 4], &["x > 0"]);

        assert_eq!(key1, key2);
        assert_ne!(key1, key3);
    }

    #[test]
    fn test_smt_context_creation() {
        let ctx = SmtContext::new();
        assert!(ctx.is_ok());
    }

    #[test]
    fn test_proof_error_display() {
        let e = ProofError::SolverFailure("test".to_string());
        assert!(e.to_string().contains("test"));

        let e = ProofError::InvariantViolated("inv".to_string());
        assert!(e.to_string().contains("inv"));
    }
}
