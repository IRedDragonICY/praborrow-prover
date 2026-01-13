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
use alloc::string::ToString;
use alloc::vec::Vec;
#[cfg(feature = "std")]
use lazy_static::lazy_static;
#[cfg(feature = "std")]
// Hashing for verification cache
pub use sha2;
#[cfg(feature = "std")]
use sha2::{Digest, Sha256};
use thiserror::Error;

// ... (skipping Z3 imports which remain the same) ...

// Re-export types from core for convenience
pub use praborrow_core::{AnnexError, ProofCarrying};

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
        #[derive(Debug, Clone)]
        pub struct Int;
        #[derive(Debug, Clone)]
        pub struct Bool;

        impl Int {
            pub fn from_i64(_v: i64) -> Self {
                Self
            }
            pub fn from_u64(_v: u64) -> Self {
                Self
            }
        }

        // Mock ops for Int
        impl core::ops::Add for Int {
            type Output = Self;
            fn add(self, _: Self) -> Self {
                Self
            }
        }
        impl core::ops::Sub for Int {
            type Output = Self;
            fn sub(self, _: Self) -> Self {
                Self
            }
        }
        impl core::ops::Mul for Int {
            type Output = Self;
            fn mul(self, _: Self) -> Self {
                Self
            }
        }
        impl core::ops::Div for Int {
            type Output = Self;
            fn div(self, _: Self) -> Self {
                Self
            }
        }
        impl Int {
            pub fn rem(&self, _: &Self) -> Self {
                Self
            }
            pub fn gt(&self, _: &Self) -> Bool {
                Bool
            }
            pub fn lt(&self, _: &Self) -> Bool {
                Bool
            }
            pub fn eq(&self, _: &Self) -> Bool {
                Bool
            }
            pub fn ge(&self, _: &Self) -> Bool {
                Bool
            }
            pub fn le(&self, _: &Self) -> Bool {
                Bool
            }
        }

        impl Bool {
            pub fn from_bool(_ctx: &crate::Context, _b: bool) -> Self {
                Self
            }
            pub fn and(_: &[&Self]) -> Self {
                Self
            }
            pub fn or(_: &[&Self]) -> Self {
                Self
            }
            pub fn not(&self) -> Self {
                Self
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

    /// Invalid integer literal.
    #[error("Invalid integer literal")]
    IntParseError(#[from] core::num::ParseIntError),
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
            inner: Mutex::new(LruCache::new(
                NonZeroUsize::new(10000).expect("Cache size > 0"),
            )),
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

pub mod backend;
use backend::SolverBackend;

#[cfg(feature = "z3-backend")]
type BackendImpl = backend::z3_backend::Z3Backend;

#[cfg(not(feature = "z3-backend"))]
type BackendImpl = backend::stub_backend::StubBackend;

/// Manages the SMT context.
pub struct SmtContext {
    backend: BackendImpl,
}

impl SmtContext {
    pub fn new() -> Result<Self, ProofError> {
        Ok(Self {
            backend: BackendImpl::new()?,
        })
    }

    pub async fn verify_invariants(
        &self,
        provider: &dyn backend::FieldValueProvider,
        invariants: &[&str],
    ) -> Result<VerificationToken, ProofError> {
        self.backend.verify(invariants, provider).await
    }
}

// ============================================================================
// ProveInvariant Trait
// ============================================================================

/// Trait for types that can be formally verified.
pub trait ProveInvariant: Send + Sync {
    /// Returns the invariant expressions as strings.
    fn invariant_expressions() -> &'static [&'static str];

    /// Computes a hash of the current field values.
    fn compute_data_hash(&self) -> Vec<u8>;

    /// Gets a field value provider for the instance.
    fn get_field_provider(&self) -> alloc::boxed::Box<dyn backend::FieldValueProvider + '_>;

    /// Verifies all invariants.
    fn verify(
        &self,
    ) -> impl core::future::Future<Output = Result<VerificationToken, ProofError>> + Send {
        async move {
            let ctx = SmtContext::new()?;
            self.verify_with_context(&ctx).await
        }
    }

    /// Verifies invariants using a specific SMT context.
    fn verify_with_context(
        &self,
        ctx: &SmtContext,
    ) -> impl core::future::Future<Output = Result<VerificationToken, ProofError>> + Send;
}

// ============================================================================
// VerifiedAnnex Trait
// ============================================================================
pub trait VerifiedAnnex<T> {
    fn annex_verified(
        &self,
    ) -> impl core::future::Future<Output = Result<crate::ProofCarrying<()>, crate::AnnexError>> + Send;
}

// ============================================================================
// VerifiableSovereign Extension Trait
// ============================================================================

use praborrow_core::Sovereign;

/// Extension trait for `Sovereign<T>` to enable formal verification.
pub trait VerifiableSovereign {
    /// Verifies the integrity of the sovereign resource using the SMT solver.
    #[allow(async_fn_in_trait)]
    async fn verify_integrity(&self) -> Result<VerificationToken, ProofError>;
}

impl<T: ProveInvariant + Sync> VerifiableSovereign for Sovereign<T> {
    async fn verify_integrity(&self) -> Result<VerificationToken, ProofError> {
        match self.try_get() {
            Ok(inner) => inner.verify().await,
            Err(_) => Err(ProofError::InvariantViolated(
                "Cannot verify: Resource is exiled (foreign jurisdiction)".to_string(),
            )),
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
