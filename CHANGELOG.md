# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## Unreleased

### Breaking Changes

- Deserializer: Will throw an error if recursing past the depth limit, defaults to 128.

### Added

- Deserializer: Disable calls to `toJSON` with `Deserializer::without_to_json()`
- Deserializer: Recursion limit is now finite and controlled with `Deserializer::with_recursion_limit()`

### Changed

- Deserializer: Pass an empty-string key to root-level `toJSON` hooks instead of calling them without arguments.
- Updated to `rquickjs` version `0.15.0`

### Deprecated

### Removed

### Fixed

- Deserializer: Apply `toJSON` only once per value position, preventing infinite recursion when a hook returns `this` or another object with a hook.
- Deserializer: Honor root-level `toJSON` hooks on arrays and boxed primitives, and when deserializing options and enums.

### Security
