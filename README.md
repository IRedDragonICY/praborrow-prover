# praborrow-prover

Formal verification engine for the PraBorrow framework.

## Overview

This crate provides the constraint solving and proof generation capabilities for PraBorrow. It integrates with Z3 to verify invariants specified in `praborrow-defense` at both compile-time and runtime.

## Key Features

- **Z3 Integration**: Bindings to the Z3 theorem prover for SMT solving.
- **Invariant Parsing**: Parsing logic for logical assertions defined in contracts.
- **Validity Checking**: Automated verification of boolean expressions against sovereign state.

---

# praborrow-prover (Bahasa Indonesia)

Mesin verifikasi formal untuk framework PraBorrow.

## Ikhtisar (Overview)

Crate ini menyediakan kemampuan penyelesaian batasan (constraint solving) dan pembuatan bukti (proof generation) untuk PraBorrow. Crate ini berintegrasi dengan Z3 untuk memverifikasi invarian yang ditentukan dalam `praborrow-defense` baik pada saat kompilasi (compile-time) maupun waktu aktif (runtime).

## Fitur Utama (Key Features)

- **Integrasi Z3**: Binding ke theorem prover Z3 untuk penyelesaian SMT (SMT solving).
- **Parsing Invarian**: Logika parsing untuk asersi logis yang didefinisikan dalam kontrak.
- **Pemeriksaan Validitas**: Verifikasi otomatis ekspresi boolean terhadap status kedaulatan (sovereign state).

