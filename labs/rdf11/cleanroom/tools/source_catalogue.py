#!/usr/bin/env python3
"""Locate human-selected passages; generate a DRAFT scalar partition, never approvals.
Uses HTMLParser only as a source locator, not as an HTML5 DOM or assertion extractor.
Reads original bytes without newline/Unicode normalization.
"""
from pathlib import Path
from html.parser import HTMLParser
from hashlib import sha256
import json
import sys

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT.parent
SOURCES = {
    "mt": ("rdf11-mt-20140225.html", "a4bc1dc53bc66fb7d57cd4b646e2527e35dbcce74fc54d8dd59beb255a830f80",
           "https://www.w3.org/TR/2014/REC-rdf11-mt-20140225/"),
    "concepts": ("rdf11-concepts-20140225.html", "3838c992097f72ee8784b6c96194d9879f86f2e08f53ced5a05aa4031750c5ac",
                 "https://www.w3.org/TR/2014/REC-rdf11-concepts-20140225/"),
    "rfc5646": ("rfc5646-200909.html", "b184da959296601926af6723163b89dcc1f50a39c27f8abbf8b46de905d75a39",
                "https://www.rfc-editor.org/rfc/rfc5646.html")
}
SOURCE_TITLES = {"mt": "RDF 1.1 Semantics", "concepts": "RDF 1.1 Concepts",
                 "rfc5646": "RFC 5646 · imported language-tag syntax"}
def digest(data):
    return sha256(data).hexdigest()

def normalized(text):
    return " ".join(text.split())

class Locator(HTMLParser):
    VOID = {"area", "base", "br", "col", "embed", "hr", "img", "input",
            "link", "meta", "param", "source", "track", "wbr"}
    def __init__(self, source):
        super().__init__(convert_charrefs=True)
        self.source = source
        self.starts = [0] + [i+1 for i, ch in enumerate(source) if ch == "\n"]
        self.stack, self.nodes = [], []
        self.feed(source)
        self.close()
    def scalar_offset(self):
        line, column = self.getpos()
        return self.starts[line-1] + column
    def handle_starttag(self, tag, attrs):
        node = {"tag": tag, "attrs": dict(attrs), "start": self.scalar_offset(), "text": ""}
        node["ancestors"] = [n["attrs"].get("id") for n in self.stack]
        if tag in self.VOID:
            node["end"] = node["start"] + len(self.get_starttag_text())
            self.nodes.append(node)
        else:
            self.stack.append(node)
    def handle_startendtag(self, tag, attrs):
        self.handle_starttag(tag, attrs)
        if tag not in self.VOID:
            node = self.stack.pop()
            node["end"] = node["start"] + len(self.get_starttag_text())
            self.nodes.append(node)
    def handle_endtag(self, tag):
        for i in range(len(self.stack)-1, -1, -1):
            if self.stack[i]["tag"] == tag:
                end = self.source.index(">", self.scalar_offset()) + 1
                for node in self.stack[i:]:
                    node["end"] = end
                    self.nodes.append(node)
                del self.stack[i:]
                break
    def handle_data(self, data):
        for node in self.stack:
            node["text"] += data
    def select(self, selector):
        candidates = [n for n in self.nodes if n["tag"] == selector["tag"]
                      and (normalized(selector["text"]) == normalized(n["text"])
                           if selector.get("exact_text", False)
                           else normalized(selector["text"]) in normalized(n["text"]))
                      and ("within_section" not in selector
                           or selector["within_section"] in n["ancestors"])
                      and ("element_id" not in selector
                           or n["attrs"].get("id") == selector["element_id"])]
        if len(candidates) != 1:
            raise ValueError(f"{selector['id']}: expected one passage, found {len(candidates)}")
        return candidates[0]

def produce():
    review = json.loads((ROOT / "catalogue/mapping-review.json").read_text())
    inventory = json.loads((LEAN / "ledger/semantics-inventory.json").read_text())
    records = {r["id"]: dict(r) for r in inventory["records"]}
    mappings = {r["claim_id"]: r for r in review["mappings"]}
    assert len(records) == len(inventory["records"]), "Duplicate claim IDs"
    assert len(mappings) == len(review["mappings"]), "Duplicate mapping IDs"
    docs, parsers, texts, passages = {}, {}, {}, []
    for key, (filename, expected, url) in SOURCES.items():
        raw = (LEAN / "specifications" / filename).read_bytes()
        assert digest(raw) == expected, f"Source hash changed: {filename}"
        text = raw.decode("utf-8", errors="strict")
        assert not any(0xD800 <= ord(c) <= 0xDFFF for c in text)
        # Explicit boundary conversion tables: scalars -> bytes and UTF-16 units.
        byte_offsets, utf16_offsets = [0], [0]
        for ch in text:
            byte_offsets.append(byte_offsets[-1] + len(ch.encode("utf-8")))
            utf16_offsets.append(utf16_offsets[-1] + (2 if ord(ch) > 0xFFFF else 1))
        docs[key] = {
            "id": key, "title": SOURCE_TITLES[key],
            "path": "../specifications/" + filename, "url": url,
            "sha256": expected, "bytes": len(raw), "scalars": len(text),
            "decoding": "strict UTF-8; no normalization; CR and LF retained separately",
            "coordinate_unit": "Unicode scalar value", "interval_convention": "[start,end)",
            "byte_boundaries_sha256": digest(json.dumps(byte_offsets).encode()),
            "utf16_boundaries_sha256": digest(json.dumps(utf16_offsets).encode()),
            "locator": "Python stdlib html.parser.HTMLParser; not an HTML5 DOM",
            "python_version": sys.version.split()[0]
        }
        parsers[key], texts[key] = Locator(text), text
    for selector in review["passage_selectors"]:
        key = selector["source"]
        n = parsers[key].select(selector)
        start, end = n["start"], n["end"]
        passage = {
            "id": selector["id"], "source": key, "source_sha256": docs[key]["sha256"],
            "start": start, "end": end, "claims": selector["claims"],
            "slice_sha256": digest(texts[key][start:end].encode("utf-8")),
            "locator_tag": n["tag"], "review": "pending",
            "scope_note": "Association with this full HTML source element is not a claim that every assertion in the element has been extracted."
        }
        passages.append(passage)
        for claim in selector["claims"]:
            assert claim in records, claim
    for key, doc in docs.items():
        relevant = [p for p in passages if p["source"] == key]
        boundaries = sorted({0, doc["scalars"]} | {n for p in relevant for n in [p["start"], p["end"]]})
        atoms = []
        for start, end in zip(boundaries, boundaries[1:]):
            claims = sorted({c for p in relevant if p["start"] <= start and end <= p["end"]
                             for c in p["claims"]})
            atoms.append({"start": start, "end": end,
                          "refs": claims or ["UNRESOLVED-" + key],
                          "disposition": "claim_passage_pending_review" if claims else "unresolved"})
        doc["atoms"] = atoms
        doc["accepted_accountability_certificate"] = False
    for cid, r in records.items():
        r["cleanroom_mapping"] = mappings.get(cid)
        r["passages"] = [p["id"] for p in passages if cid in p["claims"]]
        r["extraction_review"] = "pending"
        r["formalization_review"] = "pending" if cid in mappings else "not_started"
    catalogue = {
        "schema_version": 1, "status": "draft_not_complete_coverage",
        "method": review["selection_method"],
        "source_inventory": "../ledger/semantics-inventory.json",
        "inventory_sha256": digest((LEAN / "ledger/semantics-inventory.json").read_bytes()),
        "mapping_input_sha256": digest((ROOT / "catalogue/mapping-review.json").read_bytes()),
        "documents": list(docs.values()), "passages": passages,
        "claims": list(records.values()), "context_resolutions": review["context_resolutions"],
        "dispositions": [{"id": "UNRESOLVED-" + key, "source": key,
                          "disposition": "unresolved", "review": "pending",
                          "reason": "No claim extraction has yet been assigned to this source interval."}
                         for key in docs],
        "trust": ["SHA-256 implementation in Python hashlib", "Python strict UTF-8 decoder",
                  "Python scalar indexing and source locator", "this data generator",
                  "Lean kernel and explicitly audited logical axioms"],
        "limits": ["All expert approvals are pending.",
                   "Unresolved characters remain explicitly unresolved.",
                   "The Lean partition theorem proves only structural uniqueness and valid record IDs.",
                   "Digest and decoding bindings are externally checked, not proved in Lean.",
                   "No connection to Factoidal JS/WASM or the published npm artifact is proved."]
    }
    ids = sorted(records) + ["UNRESOLVED-" + key for key in SOURCES]
    out = ["/- Generated by tools/source_catalogue.py. DRAFT; unresolved records are intentional. -/",
           "import Audit.Coverage", "", "namespace Spec2Lean.Snapshot",
           "set_option maxRecDepth 10000", "set_option maxHeartbeats 2000000",
           "def ids : List String := " + json.dumps(ids), ""]
    for key, doc in docs.items():
        out += [f'def {key}SHA256 : String := "{doc["sha256"]}"',
                f'def {key}Atoms : List Atom := [']
        out += [f'  ⟨{a["start"]}, {a["end"]}, {json.dumps(a["refs"])}⟩'
                + ("," if i < len(doc["atoms"])-1 else "")
                for i, a in enumerate(doc["atoms"])]
        out += ["]", f'theorem {key}_valid : ValidPartition ids {doc["scalars"]} 0 {key}Atoms := by decide',
                f'theorem {key}_all_positions (i : Nat) (hi : i < {doc["scalars"]}) :',
                f'    ∃ a, a ∈ {key}Atoms ∧ Contains a i ∧',
                f'      ∀ b, b ∈ {key}Atoms → Contains b i → b = a :=',
                f'  partition_sound {key}_valid i ⟨Nat.zero_le i, hi⟩',
                f'theorem {key}_references {{a : Atom}} (ha : a ∈ {key}Atoms) :',
                '    a.refs ≠ [] ∧ ∀ r ∈ a.refs, r ∈ ids :=',
                f'  references_grounded {key}_valid ha', ""]
    out += ["end Spec2Lean.Snapshot", ""]
    return {"catalogue/claims.json": json.dumps(catalogue, indent=2, ensure_ascii=False) + "\n",
            "Audit/Snapshot.lean": "\n".join(out)}

def main():
    check = "--check" in sys.argv
    for path, content in produce().items():
        target = ROOT / path
        if check:
            assert target.read_bytes() == content.encode("utf-8"), f"Stale generated file: {path}"
        else:
            target.write_bytes(content.encode("utf-8"))
    print("Draft source catalogue and scalar partition: " + ("verified" if check else "generated"))

if __name__ == "__main__":
    main()

