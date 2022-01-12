# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/).

## [Unreleased]

## [8.14.0] - 2021-12-12

### Added
- Link to Persson and Coquand's TYPES 1998 paper on Gröbner bases in type theory

### Changed
- Change proofs to avoid depending on UIP, i.e., axiom `Coq.Logic.Eqdep.Eq_rect_eq.eq_rect_eq` (@SkySkimmer)

## [8.13.0] - 2021-08-01

### Added
- Proof using annotations

### Fixed
- Add hint locality

### Changed
- Non-Prop definitions are transparent
- Avoid global hint locality

## [8.11.0] - 2020-05-27
### Added
- Support for building with dune, including extraction of OCaml code
- Metadata on project, including detailed publication information

### Fixed
- Compatibility with Coq 8.11

### Changed
- Reorganize files into subdirectories
- Generalize definitions and results from Set to Type

[Unreleased]: https://github.com/coq-community/buchberger/compare/v8.14.0...master
[8.14.0]: https://github.com/coq-community/buchberger/releases/tag/v8.14.0
[8.13.0]: https://github.com/coq-community/buchberger/releases/tag/v8.13.0
[8.11.0]: https://github.com/coq-community/buchberger/releases/tag/v8.11.0
