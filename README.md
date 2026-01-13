# praborrow-prover

English | [Indonesia](./README_ID.md)

Formal verification engine for the PraBorrow framework.

## Overview

This crate provides the constraint solving and proof generation capabilities for PraBorrow. It integrates with Z3 to verify invariants specified in `praborrow-defense` at both compile-time and runtime.

## Key Features

- **Z3 Integration**: Bindings to the Z3 theorem prover for SMT solving.
- **Invariant Parsing**: Parsing logic for logical assertions defined in contracts.
- **Validity Checking**: Automated verification of boolean expressions against sovereign state.


