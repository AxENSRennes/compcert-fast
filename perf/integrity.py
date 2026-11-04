"""Checks anchored to Git objects, complementary to independent Coq checking."""
from collections import Counter
import hashlib
import io
import json
import re
import subprocess

UPSTREAM = "14d616046360a0b2611ebdfc2f98368af402e1f7"
ASSUMPTIONS_BASE = "befa8484ea29fe73a90785983541fb45745c26a0"
REVIEWED_FORMAL = {"backend/Linearize.v", "backend/Linearizeproof.v"}
ORACLES = {"backend/Regalloc.ml", "backend/Inliningaux.ml", "backend/Linearizeaux.ml"}
BUILD_FILES = {"Makefile", "Makefile.extr", "Makefile.menhir", "configure"}


def sha(data):
    return hashlib.sha256(data).hexdigest()


def upstream_sources(root):
    listing = subprocess.check_output(["git", "ls-tree", "-rz", UPSTREAM], cwd=root)
    selected = {}
    for entry in listing.split(b"\0"):
        if entry:
            header, name = entry.split(b"\t", 1)
            _, kind, oid = header.split()
            name = name.decode()
            if kind == b"blob" and (name.endswith((".v", ".vp", ".ml", ".mli"))
                                     or name == "LICENSE" or name in BUILD_FILES):
                selected[name] = oid
    ids = list(dict.fromkeys(selected.values()))
    stream = io.BytesIO(subprocess.check_output(["git", "cat-file", "--batch"], cwd=root,
                                               input=b"\n".join(ids) + b"\n"))
    blobs = {}
    for oid in ids:
        returned, kind, length = stream.readline().split()
        if returned != oid or kind != b"blob":
            raise ValueError("Unexpected upstream git object")
        blobs[oid] = stream.read(int(length))
        if stream.read(1) != b"\n":
            raise ValueError("Malformed git object stream")
    return {name: blobs[oid] for name, oid in selected.items()}


def coq_code(source, hide_strings=False):
    """Remove nested comments; optionally hide strings before lexical checks."""
    out, index, depth = [], 0, 0
    while index < len(source):
        if source.startswith("(*", index):
            depth += 1
            out.append(" ")
            index += 2
        elif depth and source.startswith("*)", index):
            depth -= 1
            index += 2
        elif depth:
            out.append("\n" if source[index] == "\n" else " ")
            index += 1
        elif source[index] == '"':
            start = index
            index += 1
            while index < len(source):
                if source[index] == '"':
                    index += 1
                    if index < len(source) and source[index] == '"':
                        index += 1
                        continue
                    break
                index += 1
            text = source[start:index]
            out.append(" " * len(text) if hide_strings else text)
        else:
            out.append(source[index])
            index += 1
    if depth:
        raise ValueError("Unclosed Coq comment")
    return "".join(out)


def declarations(source):
    pattern = r"\b(?:Lemma|Theorem|Corollary|Fact|Remark|Proposition|Example)\s+(\w+)\b(.*?)\bProof\s*\."
    return {name: " ".join(statement.split())
            for name, statement in re.findall(pattern, coq_code(source), re.S)}


def assumption_commands(source):
    pattern = (r"\b(?:Axioms?|Parameters?|Conjectures?|Hypotheses|Hypothesis|Variables?|Context|"
               r"Declare|Primitive|Admit|Admitted|admit|Load|Require)\b.*?\.(?=\s|$)|"
               r"\b\w*_no_check\b|\bUnset\s+(?:Guard|Positivity|Universe)\s+Checking\b|"
               r"\bSet\s+[^.]*\bType\s+In\s+Type\b")
    return Counter(" ".join(item.split()) for item in
                   re.findall(pattern, coq_code(source, hide_strings=True), re.S))


def reviewed_change_safe(original, current):
    old, new = declarations(original), declarations(current)
    return (all(new.get(name) == statement for name, statement in old.items())
            and assumption_commands(original) == assumption_commands(current))


def canonical_assumptions(text):
    result = []
    for block in text.split("Axioms:")[1:]:
        entries = re.findall(r"^([A-Za-z_][\w.']*)\s*:\s*(.*?)(?=^[A-Za-z_][\w.']*\s*:|\Z)",
                             block, re.M | re.S)
        if not entries:
            raise ValueError("Cannot parse principal theorem assumptions")
        result.append({name: " ".join(typ.split()) for name, typ in entries})
    if len(result) != 2:
        raise ValueError("Expected assumptions for both principal theorems")
    return result


def check_principal_assumptions(root, actual):
    original = subprocess.check_output(
        ["git", "show", f"{ASSUMPTIONS_BASE}:perf/results/assumptions.txt"], cwd=root, text=True)
    if canonical_assumptions(actual) != canonical_assumptions(original):
        raise ValueError("Principal theorem assumptions differ from the original checked baseline")
