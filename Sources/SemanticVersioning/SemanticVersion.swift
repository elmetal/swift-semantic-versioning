/// [Semantic Versioning 2.0.0](https://semver.org/spec/v2.0.0.html) のバージョン。
///
/// 仕様の BNF で妥当な文字列からだけ作れる。数値部分に桁数の上限はない。
///
/// ```swift
/// let a = SemanticVersion("1.0.0-rc.1")!
/// let b = SemanticVersion("1.0.0")!
/// a < b  // true
/// ```
///
/// 比較と等価性は仕様 §11 の優先順位に従う。ビルドメタデータは優先順位に影響しないので、
/// `1.0.0+a` と `1.0.0+b` は `==` で等しい。ビルドメタデータまで含めて比べるには `isIdentical(to:)` を使う。
public struct SemanticVersion: Sendable {
    /// 不変条件: `components.isWellFormed`。
    /// 入るのは `Parser.parse` の結果か、妥当性を保つと証明済みの操作の結果だけである。
    let components: Components

    /// 妥当な構成要素からバージョンを作る。
    init(wellFormed components: Components) {
        assert(components.isWellFormed)
        self.components = components
    }

    /// 数値からバージョンを作る。プレリリースとビルドメタデータは付かない。
    ///
    /// ```swift
    /// SemanticVersion(major: 1, minor: 2, patch: 3).description  // "1.2.3"
    /// ```
    ///
    /// `UInt` に収まらない値は、文字列から作る。
    public init(major: UInt, minor: UInt, patch: UInt) {
        // Lean: `Version.toComponents`(妥当性は `Version.WF.toComponents_wf`)
        self.init(wellFormed: Components(
            major: Digits.decimal(major),
            minor: Digits.decimal(minor),
            patch: Digits.decimal(patch),
            preRelease: [],
            build: []))
    }

    /// UTF-8 のバイト列からバージョンを作る。仕様の BNF で妥当でなければ `nil`。
    public init?(utf8 bytes: some Sequence<UInt8>) {
        guard let components = Parser.parse(Array(bytes)[...]) else {
            return nil
        }
        self.components = components
    }
}

// MARK: - 文字列との変換

extension SemanticVersion: LosslessStringConvertible {
    /// 文字列からバージョンを作る。仕様の BNF で妥当でなければ `nil`。
    public init?(_ description: String) {
        self.init(utf8: description.utf8)
    }

    /// バージョン文字列。作るときに渡した文字列と一致する。
    public var description: String {
        String(decoding: Parser.render(components), as: UTF8.self)
    }
}

// MARK: - 構成要素

extension SemanticVersion {
    /// メジャーバージョンの 10 進表記。桁数に上限がないので文字列で返す。
    public var major: String {
        String(decoding: components.major, as: UTF8.self)
    }

    /// マイナーバージョンの 10 進表記。
    public var minor: String {
        String(decoding: components.minor, as: UTF8.self)
    }

    /// パッチバージョンの 10 進表記。
    public var patch: String {
        String(decoding: components.patch, as: UTF8.self)
    }

    /// プレリリース識別子。プレリリース版でなければ空。
    public var prereleaseIdentifiers: [String] {
        components.preRelease.map { String(decoding: $0, as: UTF8.self) }
    }

    /// ビルドメタデータの識別子。なければ空。
    public var buildMetadataIdentifiers: [String] {
        components.build.map { String(decoding: $0, as: UTF8.self) }
    }

    /// プレリリース版かどうか。
    public var isPrerelease: Bool {
        !components.preRelease.isEmpty
    }
}

// MARK: - 繰り上げ

extension SemanticVersion {
    /// パッチの繰り上げ: このバージョンより高い通常バージョンのうち、最も低いもの。
    ///
    /// 通常バージョンならパッチを 1 上げる。プレリリース版なら、対応する通常バージョンになる。
    /// 結果にプレリリースとビルドメタデータは付かない。
    ///
    /// ```swift
    /// SemanticVersion("1.2.3")!.nextPatch       // 1.2.4
    /// SemanticVersion("1.2.3-rc.1")!.nextPatch  // 1.2.3
    /// ```
    public var nextPatch: SemanticVersion {
        // Lean: `Components.WF.nextPatch_wf`
        SemanticVersion(wellFormed: Increment.nextPatch(components))
    }

    /// マイナーの繰り上げ: このバージョンより高く、パッチが 0 である通常バージョンのうち、最も低いもの。
    ///
    /// ```swift
    /// SemanticVersion("1.2.3")!.nextMinor       // 1.3.0
    /// SemanticVersion("1.2.3-rc.1")!.nextMinor  // 1.3.0
    /// SemanticVersion("1.2.0-rc.1")!.nextMinor  // 1.2.0
    /// ```
    public var nextMinor: SemanticVersion {
        // Lean: `Components.WF.nextMinor_wf`
        SemanticVersion(wellFormed: Increment.nextMinor(components))
    }

    /// メジャーの繰り上げ: このバージョンより高く、マイナーとパッチが 0 である通常バージョンのうち、最も低いもの。
    ///
    /// ```swift
    /// SemanticVersion("1.2.3")!.nextMajor       // 2.0.0
    /// SemanticVersion("1.2.0-rc.1")!.nextMajor  // 2.0.0
    /// SemanticVersion("2.0.0-rc.1")!.nextMajor  // 2.0.0
    /// ```
    public var nextMajor: SemanticVersion {
        // Lean: `Components.WF.nextMajor_wf`
        SemanticVersion(wellFormed: Increment.nextMajor(components))
    }
}

// MARK: - 優先順位

extension SemanticVersion: Comparable {
    /// 優先順位が等しい。ビルドメタデータは無視する。
    public static func == (lhs: SemanticVersion, rhs: SemanticVersion) -> Bool {
        Precedence.precedenceEqual(lhs.components, rhs.components)
    }

    /// 左辺の優先順位が右辺より低い。
    public static func < (lhs: SemanticVersion, rhs: SemanticVersion) -> Bool {
        Precedence.less(lhs.components, rhs.components)
    }
}

extension SemanticVersion {
    /// ビルドメタデータまで含めて同じバージョンかどうか。`description` が等しいことと同じ。
    ///
    /// `==` は優先順位の等しさで、ビルドメタデータを無視する。
    ///
    /// ```swift
    /// let a = SemanticVersion("1.0.0+a")!
    /// let b = SemanticVersion("1.0.0+b")!
    /// a == b                // true
    /// a.isIdentical(to: b)  // false
    /// ```
    public func isIdentical(to other: SemanticVersion) -> Bool {
        // Lean: 構成要素の等しさ(`Components.eq_iff_render_eq`)
        components == other.components
    }
}

extension SemanticVersion: Hashable {
    /// `==` と整合するよう、ビルドメタデータはハッシュに含めない。
    public func hash(into hasher: inout Hasher) {
        hasher.combine(components.major)
        hasher.combine(components.minor)
        hasher.combine(components.patch)
        hasher.combine(components.preRelease)
    }
}
