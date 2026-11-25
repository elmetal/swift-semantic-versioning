# swift-semantic-versioning

[![CI](https://github.com/elmetal/swift-semantic-versioning/actions/workflows/ci.yml/badge.svg)](https://github.com/elmetal/swift-semantic-versioning/actions/workflows/ci.yml)

English | [日本語](README.ja.md)

A Swift implementation of [Semantic Versioning 2.0.0](https://semver.org/spec/v2.0.0.html): parsing, precedence, and incrementing.

- **Strict.** Accepts exactly the strings that are valid under the specification's grammar.
- **No size limit.** Numeric identifiers are kept as digit strings, so `18446744073709551616.0.0` parses, compares, and increments correctly.
- **Specified in Lean.** The behavior is defined in Lean 4 and proven to match the specification. The Swift code mirrors those definitions. See [Verification](#verification).
- **No dependencies.** The library does not import Foundation.

## Requirements

Swift 6.4 or later. CI runs on macOS and Linux.

## Installation

Add the package to your `Package.swift`:

```swift
dependencies: [
    .package(url: "https://github.com/elmetal/swift-semantic-versioning.git", from: "0.1.0"),
],
targets: [
    .target(
        name: "YourTarget",
        dependencies: [
            .product(name: "SemanticVersioning", package: "swift-semantic-versioning"),
        ]
    ),
]
```

## Usage

```swift
import SemanticVersioning
```

### Parsing

`SemanticVersion` can only be created from a valid version, so a value is always well-formed.

```swift
let version = SemanticVersion("1.2.3-rc.1+build.5")!

version.major                     // "1"
version.minor                     // "2"
version.patch                     // "3"
version.prereleaseIdentifiers     // ["rc", "1"]
version.buildMetadataIdentifiers  // ["build", "5"]
version.isPrerelease              // true
version.description               // "1.2.3-rc.1+build.5"
```

Anything outside the grammar is rejected. There is no lenient mode.

```swift
SemanticVersion("1.2")       // nil: three numbers are required
SemanticVersion("v1.2.3")    // nil: no prefix
SemanticVersion("01.2.3")    // nil: no leading zeros
SemanticVersion("1.2.3-01")  // nil: no leading zeros in a numeric pre-release identifier
SemanticVersion("1.2.3+01")  // valid: build identifiers may have leading zeros
SemanticVersion(" 1.2.3")    // nil: no surrounding whitespace
```

`major`, `minor`, and `patch` are strings because the specification puts no upper bound on them. Convert when you need a number:

```swift
UInt(version.major)  // Optional(1)
```

You can also parse UTF-8 bytes directly with `SemanticVersion(utf8:)`.

### Creating from numbers

```swift
SemanticVersion(major: 1, minor: 2, patch: 3).description  // "1.2.3"
```

### Comparing

`SemanticVersion` is `Comparable` and `Hashable`. The order is the precedence defined in section 11 of the specification.

```swift
let versions = ["1.0.0", "1.0.0-rc.1", "1.0.0-alpha", "1.0.0-beta.11", "1.0.0-beta.2"]
    .compactMap { SemanticVersion($0) }

versions.sorted().map(\.description)
// ["1.0.0-alpha", "1.0.0-beta.2", "1.0.0-beta.11", "1.0.0-rc.1", "1.0.0"]
```

Build metadata does not affect precedence, so `==` ignores it. Use `isIdentical(to:)` to compare everything.

```swift
let a = SemanticVersion("1.0.0+linux")!
let b = SemanticVersion("1.0.0+macos")!

a == b                // true
a.isIdentical(to: b)  // false
Set([a, b]).count     // 1
```

### Incrementing

Each operation returns the lowest release of its kind that is higher than the receiver. The result never has pre-release identifiers or build metadata.

| | Definition | `1.2.3` | `1.2.3-rc.1` | `1.2.0-rc.1` |
| --- | --- | --- | --- | --- |
| `nextPatch` | lowest normal version above the receiver | `1.2.4` | `1.2.3` | `1.2.0` |
| `nextMinor` | lowest normal version above the receiver whose patch is 0 | `1.3.0` | `1.3.0` | `1.2.0` |
| `nextMajor` | lowest normal version above the receiver whose minor and patch are 0 | `2.0.0` | `2.0.0` | `2.0.0` |

For a normal version this is the usual "add one and reset the lower parts". For a pre-release it yields the release that the pre-release leads to, when that release is of the requested kind. The results agree with `inc` in [node-semver](https://github.com/npm/node-semver).

```swift
SemanticVersion("1.2.3")!.nextMinor.description       // "1.3.0"
SemanticVersion("1.2.0-rc.1")!.nextMinor.description  // "1.2.0"
```

Incrementing cannot overflow:

```swift
let huge = SemanticVersion("18446744073709551615.0.0")!  // UInt64.max
huge.nextMajor.description                               // "18446744073709551616.0.0"
```

## Verification

The [`Formal/`](Formal/) directory contains a Lean 4 formalization of the specification. You do not need Lean to use the package.

- **Proven in Lean, for all inputs.** The reference parser accepts exactly the specification's grammar. Precedence is a total order once build metadata is ignored. Comparing digit strings by length and then lexicographically agrees with comparing numbers. Each increment is the lowest release of its kind above the input.
- **Not proven.** That the Swift code equals the Lean definitions. The Swift functions mirror the Lean ones one-to-one, and the tests compare them against vectors generated by running the Lean definitions: every string up to 7 characters over a representative alphabet plus longer strings that extend a valid prefix (about 990,000 strings in total), and all pairs of about 1,400 sample versions.
- **Trusted.** The Swift compiler and standard library.

Details are in [`Formal/README.md`](Formal/README.md) (in Japanese).

## Development

```bash
swift test
```

To check the proofs and regenerate the test vectors, install [Lean](https://lean-lang.org/) and run:

```bash
cd Formal
lake build
lake exe vectors ../Tests/SemanticVersioningTests/Vectors
```

## License

[MIT](LICENSE)

The Semantic Versioning specification is by Tom Preston-Werner and is licensed under [CC BY 3.0](https://creativecommons.org/licenses/by/3.0/).
