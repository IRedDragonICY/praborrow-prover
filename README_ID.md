# praborrow-prover (Bahasa Indonesia)

[English](./README.md) | Indonesia

Mesin verifikasi formal untuk framework PraBorrow.

## Ikhtisar (Overview)

Crate ini menyediakan kemampuan penyelesaian batasan (constraint solving) dan pembuatan bukti (proof generation) untuk PraBorrow. Crate ini berintegrasi dengan Z3 untuk memverifikasi invarian yang ditentukan dalam `praborrow-defense` baik pada saat kompilasi (compile-time) maupun waktu aktif (runtime).

## Fitur Utama (Key Features)

- **Integrasi Z3**: Binding ke theorem prover Z3 untuk penyelesaian SMT (SMT solving).
- **Parsing Invarian**: Logika parsing untuk asersi logis yang didefinisikan dalam kontrak.
- **Pemeriksaan Validitas**: Verifikasi otomatis ekspresi boolean terhadap status kedaulatan (sovereign state).
