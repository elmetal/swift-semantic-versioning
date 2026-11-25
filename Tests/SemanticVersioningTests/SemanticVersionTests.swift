import Testing

@testable import SemanticVersioning

@Suite("文字列との変換")
struct ParsingTests {
    @Test("妥当な文字列は読めて、文字列に戻すと元に戻る", arguments: [
        "0.0.0",
        "1.2.3",
        "10.20.30",
        "1.0.0-alpha",
        "1.0.0-alpha.1",
        "1.0.0-0.3.7",
        "1.0.0-x.7.z.92",
        "1.0.0-x-y-z.--",
        "1.0.0-alpha+001",
        "1.0.0+20130313144700",
        "1.0.0-beta+exp.sha.5114f85",
        "1.0.0+21AF26D3----117B344092BD",
        "1.0.0-0a",
        "1.0.0+00",
        "99999999999999999999999.999999999999999999.99999999999999999",
    ])
    func valid(_ string: String) throws {
        let version = try #require(SemanticVersion(string))
        #expect(version.description == string)
        #expect(String(version) == string)
    }

    @Test("妥当でない文字列は読めない", arguments: [
        "",
        "1",
        "1.2",
        "1.2.3.4",
        "01.2.3",
        "1.02.3",
        "1.2.03",
        "1.2.3-",
        "1.2.3+",
        "1.2.3-01",
        "1.2.3-a..b",
        "1.2.3+a+b",
        "v1.2.3",
        " 1.2.3",
        "1.2.3 ",
        "1.2.3\n",
        "1.2.3-a_b",
        "１.2.3",
        "1.2.3-é",
    ])
    func invalid(_ string: String) {
        #expect(SemanticVersion(string) == nil)
    }

    @Test("構成要素を取り出せる")
    func components() throws {
        let version = try #require(SemanticVersion("1.20.300-rc.1+build.5"))
        #expect(version.major == "1")
        #expect(version.minor == "20")
        #expect(version.patch == "300")
        #expect(version.prereleaseIdentifiers == ["rc", "1"])
        #expect(version.buildMetadataIdentifiers == ["build", "5"])
        #expect(version.isPrerelease)

        let release = try #require(SemanticVersion("1.0.0"))
        #expect(release.prereleaseIdentifiers.isEmpty)
        #expect(release.buildMetadataIdentifiers.isEmpty)
        #expect(!release.isPrerelease)
    }

    @Test("UTF-8 のバイト列から作れる")
    func utf8() throws {
        let version = try #require(SemanticVersion(utf8: Array("1.2.3-rc.1".utf8)))
        #expect(version.description == "1.2.3-rc.1")
        #expect(SemanticVersion(utf8: [0x31, 0x2E, 0x30, 0x2E, 0xFF]) == nil)
        #expect(SemanticVersion(utf8: [] as [UInt8]) == nil)
    }
}

@Suite("優先順位")
struct PrecedenceTests {
    /// 並びが優先順位について狭義単調増加であることを確かめる。
    private func expectIncreasing(_ strings: [String]) throws {
        let versions = try strings.map { try #require(SemanticVersion($0)) }
        for i in versions.indices {
            for j in versions.indices {
                #expect((versions[i] < versions[j]) == (i < j), "\(strings[i]) < \(strings[j])")
                #expect((versions[i] == versions[j]) == (i == j), "\(strings[i]) == \(strings[j])")
            }
        }
        #expect(versions.shuffled().sorted().map(\.description) == strings)
    }

    @Test("§11.2: major, minor, patch を数値として比べる")
    func core() throws {
        try expectIncreasing(["1.0.0", "2.0.0", "2.1.0", "2.1.1"])
        try expectIncreasing(["1.9.0", "1.10.0", "1.11.0", "2.0.0", "10.0.0"])
    }

    @Test("§11.3〜§11.4: プレリリース")
    func prerelease() throws {
        try expectIncreasing([
            "1.0.0-alpha", "1.0.0-alpha.1", "1.0.0-alpha.beta", "1.0.0-beta",
            "1.0.0-beta.2", "1.0.0-beta.11", "1.0.0-rc.1", "1.0.0",
        ])
        try expectIncreasing(["1.0.0-2", "1.0.0-10", "1.0.0--", "1.0.0-A", "1.0.0-a", "1.0.0-a.2"])
    }

    @Test("整数型に収まらない桁数でも比べられる")
    func huge() throws {
        try expectIncreasing([
            "18446744073709551615.0.0",
            "18446744073709551616.0.0",
            "99999999999999999999999.0.0",
            "100000000000000000000000.0.0",
        ])
    }

    @Test("§10: ビルドメタデータは優先順位に影響しない")
    func buildMetadata() throws {
        let a = try #require(SemanticVersion("1.0.0-rc.1+a"))
        let b = try #require(SemanticVersion("1.0.0-rc.1+b.c"))
        #expect(a == b)
        #expect(!(a < b))
        #expect(!(b < a))
        #expect(a.hashValue == b.hashValue)
        #expect(Set([a, b]).count == 1)
        #expect(a.description != b.description)
    }
}

@Suite("数値からの生成と厳密な一致")
struct ConstructionTests {
    @Test("数値から作れる")
    func fromNumbers() throws {
        let version = SemanticVersion(major: 1, minor: 20, patch: 300)
        #expect(version.description == "1.20.300")
        #expect(version.isIdentical(to: try #require(SemanticVersion("1.20.300"))))
        #expect(!version.isPrerelease)
        #expect(version.buildMetadataIdentifiers.isEmpty)

        #expect(SemanticVersion(major: 0, minor: 0, patch: 0).description == "0.0.0")
        let max = SemanticVersion(major: .max, minor: .max, patch: .max)
        #expect(max.description == "\(UInt.max).\(UInt.max).\(UInt.max)")
    }

    @Test("isIdentical はビルドメタデータまで比べる")
    func identical() throws {
        let a = try #require(SemanticVersion("1.0.0-rc.1+a"))
        let b = try #require(SemanticVersion("1.0.0-rc.1+b"))
        let c = try #require(SemanticVersion("1.0.0-rc.1+a"))
        #expect(a == b)
        #expect(!a.isIdentical(to: b))
        #expect(a.isIdentical(to: c))
        #expect(a.isIdentical(to: a))
    }
}

@Suite("繰り上げ")
struct IncrementTests {
    private func next(
        _ string: String, _ keyPath: KeyPath<SemanticVersion, SemanticVersion>
    ) throws -> String {
        try #require(SemanticVersion(string))[keyPath: keyPath].description
    }

    @Test("通常バージョンは数値を 1 上げて下位を 0 に戻す")
    func normal() throws {
        #expect(try next("1.2.3", \.nextPatch) == "1.2.4")
        #expect(try next("1.2.3", \.nextMinor) == "1.3.0")
        #expect(try next("1.2.3", \.nextMajor) == "2.0.0")
        #expect(try next("1.2.9", \.nextPatch) == "1.2.10")
        #expect(try next("1.9.9", \.nextMinor) == "1.10.0")
        #expect(try next("99.99.99", \.nextMajor) == "100.0.0")
    }

    @Test("プレリリース版は、条件を満たせば対応する通常バージョンになる")
    func prerelease() throws {
        #expect(try next("1.2.3-rc.1", \.nextPatch) == "1.2.3")
        #expect(try next("1.2.3-rc.1", \.nextMinor) == "1.3.0")
        #expect(try next("1.2.0-rc.1", \.nextMinor) == "1.2.0")
        #expect(try next("1.2.0-rc.1", \.nextMajor) == "2.0.0")
        #expect(try next("2.0.0-rc.1", \.nextMajor) == "2.0.0")
        #expect(try next("1.0.0-5", \.nextMajor) == "1.0.0")
    }

    @Test("ビルドメタデータは結果に付かない")
    func buildMetadata() throws {
        #expect(try next("1.2.3+build", \.nextPatch) == "1.2.4")
        #expect(try next("1.2.3-rc.1+build", \.nextPatch) == "1.2.3")
    }

    @Test("整数型に収まらない桁数でも繰り上がる")
    func huge() throws {
        #expect(try next("1.2.18446744073709551615", \.nextPatch) == "1.2.18446744073709551616")
        #expect(
            try next("99999999999999999999999.0.0", \.nextMajor) == "100000000000000000000000.0.0")
        #expect(SemanticVersion(major: .max, minor: 0, patch: 0).nextMajor.description
            == "18446744073709551616.0.0")
    }
}
