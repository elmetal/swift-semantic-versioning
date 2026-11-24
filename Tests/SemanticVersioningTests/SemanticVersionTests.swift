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
