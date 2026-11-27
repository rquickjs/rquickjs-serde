# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## Unreleased

### Breaking Changes

### Added

### Changed

### Deprecated

### Removed

### Fixed

### Security

## [0.9.0] - 2026-11-27

### Breaking Changes

- Deserializer: Deserialization now returns a `RangeError` when exceeding the recursion limit, which defaults to 128.

### Added

- Deserializer: Disable `toJSON` lookups and calls with `Deserializer::without_to_json()`.
- Deserializer: Override the maximum recursion depth with `Deserializer::with_recursion_limit()`.

### Changed

- Deserializer: Pass an empty-string key to root-level `toJSON` hooks instead of calling them without arguments.
- Updated to `rquickjs` version `0.15.0`

### Fixed

- Deserializer: Apply `toJSON` only once per value position, avoiding repeated hook invocation on its return value and infinite recursion when a hook returns `this`.
- Deserializer: Honor root-level `toJSON` hooks on arrays and boxed primitives, and when deserializing options and enums.
