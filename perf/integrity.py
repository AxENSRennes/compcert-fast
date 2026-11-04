"""Checks anchored to Git objects, complementary to independent Coq checking."""
from collections import Counter
import hashlib
import difflib
import io
import json
import re
import subprocess

UPSTREAM = "14d616046360a0b2611ebdfc2f98368af402e1f7"
ASSUMPTIONS_BASE = "befa8484ea29fe73a90785983541fb45745c26a0"
REVIEWED_FORMAL = {"backend/Linearize.v", "backend/Linearizeproof.v",
                   "driver/Compiler.v", "driver/Compopts.v", "extraction/extraction.v",
                   "Makefile", "backend/PrintRTL.ml", "backend/Allocation.v", "backend/Allocproof.v",
                   "aarch64/SelectOp.vp", "aarch64/SelectOpproof.v", "aarch64/SelectLong.vp", "aarch64/SelectLongproof.v", "aarch64/Builtins1.v", "aarch64/Machregs.v",
                   "aarch64/Asmexpand.ml", "aarch64/TargetPrinter.ml", "aarch64/CBuiltins.ml"}
NEW_FORMAL = {"backend/Experimental.v", "backend/Experimentalproof.v",
              "backend/ExtraCleanup.v", "backend/ExtraCleanupproof.v",
              "backend/Schedule.v", "backend/Scheduleproof.v",
              "backend/HoistConst.v", "backend/HoistConstproof.v",
              "backend/LoadForward.v", "backend/LoadForwardproof.v",
              "backend/Unswitch.v", "backend/Unswitchproof.v",
              "backend/StoreElim.v", "backend/StoreElimproof.v",
              "aarch64/Neon.v", "perf/neon/Extract.v"}
COMPUTATIONAL_FLAGS = {"experimental_scalar", "experimental_unroll4", "experimental_cleanup",
                       "experimental_schedule", "experimental_hoist", "experimental_loadforward",
                       "experimental_unswitch", "experimental_select", "experimental_storeelim"}
EXTRACTION_ACCESSORS = {"experimental_scalar": "scalar_enabled", "experimental_unroll4": "unroll4_enabled",
                        "experimental_cleanup": "cleanup_enabled", "experimental_schedule": "schedule_enabled",
                        "experimental_hoist": "hoist_enabled", "experimental_loadforward": "loadforward_enabled",
                        "experimental_unswitch": "unswitch_enabled", "experimental_select": "select_enabled",
                        "experimental_storeelim": "storeelim_enabled"}
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


def reviewed_change_safe(original, current, path=None):
    if path == "extraction/extraction.v":
        return reviewed_build_safe(original, current, path)
    old, new = declarations(original), declarations(current)
    if not all(new.get(name) == statement for name, statement in old.items()):
        return False
    old_commands, new_commands = assumption_commands(original), assumption_commands(current)
    if path == "driver/Compiler.v":
        # New passes require new imports; the actual axioms and every existing
        # theorem statement remain checked, then independently kernel-checked.
        old_commands = Counter({k: v for k, v in old_commands.items() if not k.startswith("Require ")})
        new_commands = Counter({k: v for k, v in new_commands.items() if not k.startswith("Require ")})
    if path == "driver/Compopts.v":
        for command in list(new_commands):
            match = re.fullmatch(r"Parameter\s+(\w+)\s*:\s*unit\s*->\s*bool\s*\.", command)
            if match and match[1] in COMPUTATIONAL_FLAGS:
                del new_commands[command]
    if path == "backend/Allocation.v":
        original_parameters = [re.fullmatch(r"Parameter\s+regalloc\s*:\s*(.*?)\.", command)
                               for command in old_commands]
        original_type = next((match[1] for match in original_parameters if match), None)
        for command in list(new_commands):
            match = re.fullmatch(r"Parameter\s+regalloc_baseline\s*:\s*(.*?)\.", command)
            if match and match[1] == original_type:
                del new_commands[command]
    return old_commands == new_commands


def reviewed_build_safe(original, current, path):
    # These manually reviewed platform expansions are trusted OCaml, never
    # proof/kernel build recipes. Their exact contents are still hash-pinned.
    if path in {"aarch64/Asmexpand.ml", "aarch64/TargetPrinter.ml", "aarch64/CBuiltins.ml"}:
        return True
    inserted = []
    old, new = original.splitlines(keepends=True), current.splitlines(keepends=True)
    for tag, _a, _b, start, stop in difflib.SequenceMatcher(None, old, new).get_opcodes():
        if tag == "equal":
            continue
        if tag != "insert":
            return False
        inserted.extend(new[start:stop])
    addition = "".join(inserted)
    if path == "Makefile":
        allowed = {name.rsplit("/", 1)[-1] for name in NEW_FORMAL if name.startswith("backend/")}
        return all(token in allowed or token == "\\" for token in addition.split())
    if path == "extraction/extraction.v":
        code = coq_code(addition)
        code = code.replace("RTL.init_regs Op.eval_operation Op.eval_condition Op.eval_addressing", "")
        code = re.sub(r'Extract\s+Constant\s+Allocation\.regalloc_baseline\s*=>\s*"Regalloc\.regalloc_baseline"\s*\.', '', code)
        for flag, accessor in EXTRACTION_ACCESSORS.items():
            pattern = (r'Extract\s+Constant\s+Compopts\.' + flag +
                       r'\s*=>\s*"ExperimentalOptions\.' + accessor + r'"\s*\.')
            code = re.sub(pattern, "", code)
        return not code.strip()
    return path in {"backend/PrintRTL.ml", "aarch64/Asmexpand.ml",
                    "aarch64/TargetPrinter.ml", "aarch64/CBuiltins.ml"}


def new_source_safe(source):
    code = coq_code(source, hide_strings=True)
    return not re.search(r"\b(?:Axioms?|Parameters?|Conjectures?|Admit|Admitted|admit|Primitive|Declare)\b|"
                         r"\b\w*_no_check\b|\bUnset\s+(?:Guard|Positivity|Universe)\s+Checking\b|"
                         r"\bSet\s+[^.]*\bType\s+In\s+Type\b", code)


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
    old, new = canonical_assumptions(original), canonical_assumptions(actual)
    options = set()
    for before, after in zip(old, new):
        extra = {name: typ for name, typ in after.items() if name not in before}
        for name, typ in extra.items():
            option = name in {"Compopts." + flag for flag in COMPUTATIONAL_FLAGS} and typ == "unit -> bool"
            baseline_allocator = name == "Allocation.regalloc_baseline" and typ == before.get("Allocation.regalloc")
            if not option and not baseline_allocator:
                raise ValueError("New trusted principal-theorem assumption: " + name)
            options.add(name)
        if {name: typ for name, typ in after.items() if name not in extra} != before:
            raise ValueError("Original principal-theorem assumptions changed")
    return sorted(options)
