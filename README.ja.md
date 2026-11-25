# swift-semantic-versioning

[![CI](https://github.com/elmetal/swift-semantic-versioning/actions/workflows/ci.yml/badge.svg)](https://github.com/elmetal/swift-semantic-versioning/actions/workflows/ci.yml)

[English](README.md) | 日本語

[Semantic Versioning 2.0.0](https://semver.org/spec/v2.0.0.html) の Swift 実装です。バージョン文字列の解析、優先順位の比較、繰り上げを提供します。

- **厳密**: 仕様の文法で妥当な文字列だけを受け付けます。
- **桁数に上限なし**: 数値識別子を数字列のまま持つので、`18446744073709551616.0.0` も正しく解析、比較、繰り上げできます。
- **Lean で仕様を定義**: 振る舞いを Lean 4 で定義し、仕様と一致することを証明しています。Swift のコードはその定義を写したものです。詳しくは[検証](#検証)を見てください。
- **依存なし**: Foundation を import していません。

## 必要な環境

Swift 6.4 以降。CI は macOS と Linux で実行しています。

## インストール

`Package.swift` に追加します。

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

## 使い方

```swift
import SemanticVersioning
```

### 解析

`SemanticVersion` は妥当なバージョンからしか作れないので、値は常に妥当です。

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

文法から外れる文字列はすべて拒否します。緩く解釈するモードはありません。

```swift
SemanticVersion("1.2")       // nil: 数値は 3 つ必要
SemanticVersion("v1.2.3")    // nil: 接頭辞は付けられない
SemanticVersion("01.2.3")    // nil: 先頭ゼロは不可
SemanticVersion("1.2.3-01")  // nil: 数値のプレリリース識別子も先頭ゼロは不可
SemanticVersion("1.2.3+01")  // 妥当: ビルド識別子は先頭ゼロを許す
SemanticVersion(" 1.2.3")    // nil: 前後の空白は不可
```

`major`、`minor`、`patch` は文字列を返します。仕様がこれらに上限を定めていないためです。数値が必要なときは変換します。

```swift
UInt(version.major)  // Optional(1)
```

UTF-8 のバイト列から直接作る `SemanticVersion(utf8:)` もあります。

### 数値から作る

```swift
SemanticVersion(major: 1, minor: 2, patch: 3).description  // "1.2.3"
```

### 比較

`SemanticVersion` は `Comparable` と `Hashable` に適合します。順序は仕様 §11 の優先順位です。

```swift
let versions = ["1.0.0", "1.0.0-rc.1", "1.0.0-alpha", "1.0.0-beta.11", "1.0.0-beta.2"]
    .compactMap { SemanticVersion($0) }

versions.sorted().map(\.description)
// ["1.0.0-alpha", "1.0.0-beta.2", "1.0.0-beta.11", "1.0.0-rc.1", "1.0.0"]
```

ビルドメタデータは優先順位に影響しないので、`==` はビルドメタデータを無視します。すべてを比べるには `isIdentical(to:)` を使います。

```swift
let a = SemanticVersion("1.0.0+linux")!
let b = SemanticVersion("1.0.0+macos")!

a == b                // true
a.isIdentical(to: b)  // false
Set([a, b]).count     // 1
```

### 繰り上げ

どの操作も、元のバージョンより高い、その種類のリリースのうち最も低いものを返します。結果にプレリリース識別子とビルドメタデータは付きません。

| | 定義 | `1.2.3` | `1.2.3-rc.1` | `1.2.0-rc.1` |
| --- | --- | --- | --- | --- |
| `nextPatch` | 元より高い通常バージョンのうち最も低いもの | `1.2.4` | `1.2.3` | `1.2.0` |
| `nextMinor` | 元より高く、パッチが 0 の通常バージョンのうち最も低いもの | `1.3.0` | `1.3.0` | `1.2.0` |
| `nextMajor` | 元より高く、マイナーとパッチが 0 の通常バージョンのうち最も低いもの | `2.0.0` | `2.0.0` | `2.0.0` |

通常バージョンに対しては、おなじみの「1 上げて下位を 0 に戻す」と同じです。プレリリース版に対しては、そのプレリリースが目指すリリースが求める種類であれば、それを返します。結果は [node-semver](https://github.com/npm/node-semver) の `inc` と一致します。

```swift
SemanticVersion("1.2.3")!.nextMinor.description       // "1.3.0"
SemanticVersion("1.2.0-rc.1")!.nextMinor.description  // "1.2.0"
```

繰り上げでオーバーフローは起きません。

```swift
let huge = SemanticVersion("18446744073709551615.0.0")!  // UInt64.max
huge.nextMajor.description                               // "18446744073709551616.0.0"
```

## 検証

[`Formal/`](Formal/) ディレクトリに、仕様を Lean 4 で形式化したものがあります。パッケージを使うのに Lean は不要です。

- **Lean で証明済み(すべての入力について)**: 参照パーサが仕様の文法とちょうど同じ文字列を受け付けること。優先順位が、ビルドメタデータを無視すれば全順序であること。数字列を桁数、次に辞書順で比べた結果が、数値の大小と一致すること。繰り上げが、その種類のリリースのうち元より高くて最も低いものであること。
- **証明していないこと**: Swift のコードが Lean の定義と同じであること。Swift の関数は Lean の定義と 1 対 1 に対応させて書いてあり、テストでは Lean の定義を実行して生成したベクタと突き合わせています。対象は、代表の文字で作れる 7 文字以下の全文字列と、妥当な接頭辞にさらに文字を続けた文字列(合わせて約 99 万件)、それに見本のバージョン約 1,400 個のすべての組です。
- **信頼しているもの**: Swift のコンパイラと標準ライブラリ。

詳しくは [`Formal/README.md`](Formal/README.md) を見てください。

## 開発

```bash
swift test
```

証明の検査とテストベクタの再生成には [Lean](https://lean-lang.org/) を入れて、次を実行します。

```bash
cd Formal
lake build
lake exe vectors ../Tests/SemanticVersioningTests/Vectors
```

## ライセンス

[MIT](LICENSE)

Semantic Versioning の仕様は Tom Preston-Werner によるもので、[CC BY 3.0](https://creativecommons.org/licenses/by/3.0/) で提供されています。
