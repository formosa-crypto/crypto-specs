This repository provides a collection of EasyCrypt specifications
for standardized post-quantum cryptographic primitives.

It does not contain any proof of security or functional
correctness of a concrete implementation. Instead, it provides
formal specifications together with basic, general-purpose
properties of these specifications that are intended to support
and simplify subsequent formal security or correctness proofs.

This development depends on the Jasmin EasyCrypt standard
library (under the `Jasmin` namespace) as well as the EasyCrypt
proof assistant. Once these dependencies are installed, running
`make check` verifies *all* EasyCrypt files in the repository,
including the proofs. The proofs are also automatically checked
in the continuous integration (CI) pipeline.

[![CI](https://github.com/formosa-crypto/crypto-specs/actions/workflows/ci.yml/badge.svg)](https://github.com/formosa-crypto/crypto-specs/actions/workflows/ci.yml)

## Specification of the KECCAK Algorithm (SHA-3 Family)

[FIPS-202]: https://csrc.nist.gov/pubs/fips/202/final

The `fips202` directory contains an EasyCrypt formalization of the
[*SHA-3 Standard: Permutation-Based Hash and Extendable-Output Functions*][FIPS-202]
standard.

The specification is instantiated for a **1600-bit width**
(**b = 1600**), which implies the derived parameters:

- **w = b / 25 = 64**
- **l = log₂(w) = 6**

(see Table 1 of [[FIPS-202]]).

The formalization is organized into the following files:

- **Keccak-p permutation** ([Section 3 of FIPS-202][FIPS-202]) —
  `FIPS202_Keccakf1600.ec`
- **Keccak sponge construction and SHA-3 family of hash
  functions** ([Sections 4, 5, and 6 of FIPS-202][FIPS-202]) —
  `FIPS202_SHA3.ec`

Additionally, the `fips202/properties` directory contains general results
related to the specification, including:

- Equivalence proofs with respect to a complete functional specification
- Precomputation of round constants
- Precomputation of rotation offsets

In particular, it provides the following libraries:

- `fips202/properties/Keccakf1600_Spec.ec` — Functional
  specification of Keccak together with its correctness proof
- `fips202/properties/Keccak1600_Spec.ec` — A byte-oriented
  specification designed to simplify formal reasoning

## Specification of the MKEM Algorithm

[FIPS-203]: https://csrc.nist.gov/pubs/fips/203/final

The `ml-kem` directory contains an EasyCrypt formalization of the
[*Module-Lattice-Based Key-Encapsulation Mechanism Standard*][FIPS-203]
standard.

Additionally, the `ml-kem/properties` directory contains basic
properties of the ML-KEM specification aimed at easing formal
proofs.
