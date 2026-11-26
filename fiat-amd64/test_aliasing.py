#!/usr/bin/env python3
"""Check that every shipped AMD64 implementation supports in-place use."""

import concurrent.futures
import os
from pathlib import Path
import platform
import re
import shutil
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parent.parent
ASM_ROOT = ROOT / "fiat-amd64"
CC = os.environ.get("CC", "cc")


def operation(path):
    directory = path.parent.name
    if directory.endswith("_square"):
        return "square"
    if directory.endswith("_mul"):
        return "mul"
    raise ValueError("unrecognized operation: %s" % directory)


def limb_count(path):
    directory = path.parent.name
    counts = {
        "curve25519_carry": 5,
        "curve25519_solinas": 4,
        "p224": 4,
        "p256": 4,
        "p384": 6,
        "p434": 7,
        "p448_solinas_carry": 8,
        "p521_carry": 9,
        "poly1305_carry": 3,
        "secp256k1_dettman": 5,
        "secp256k1_montgomery": 4,
    }
    family = re.sub(r"^fiat_|_(?:mul|square)$", "", directory)
    return counts[family]


def symbol(path):
    for line in path.read_text().splitlines():
        match = re.match(r"\s*GLOBAL\s+(\w+)", line)
        if match:
            return match.group(1)
    raise ValueError("GLOBAL directive missing from %s" % path)


def reference_path(path):
    family = re.sub(r"^fiat_|_(?:mul|square)$", "", path.parent.name)
    family = re.sub(r"_carry$", "", family)
    return ROOT / "fiat-c" / "src" / (family + "_64.c")


def reference_symbol(sym):
    sym = sym.replace("fiat_curve25519_carry_", "fiat_25519_carry_")
    return sym.replace("fiat_p448_solinas_carry_", "fiat_p448_carry_")


def gas_source(path):
    lines = [".intel_syntax noprefix"]
    for line in path.read_text().splitlines():
        line = re.sub(r";.*$", "", line)
        if re.match(r"^\s*SECTION\s+\.text\s*$", line):
            line = ".text"
        line = re.sub(r"^\s*GLOBAL\s+(\w+)\s*$", r".globl \1", line)
        line = re.sub(
            r"\b(byte|qword|dword|word)\s+\[",
            lambda match: match.group(1).upper() + " PTR [",
            line,
            flags=re.IGNORECASE,
        )
        lines.append(line)
    lines.append('.section .note.GNU-stack,"",@progbits')
    return "\n".join(lines) + "\n"


def harness_source(sym, op, limbs, reference):
    if op == "square":
        declaration = "extern void %s(uint64_t *, const uint64_t *);" % sym
        calls = """
    %(sym)s(separate, a);
    fiat_reference(reference, a);
    if (memcmp(separate, reference, %(bytes)d) != 0) return 3;
    memcpy(inplace1, a, sizeof(a));
    %(sym)s(inplace1, inplace1);
    if (memcmp(separate, inplace1, %(bytes)d) != 0) return 1;
""" % {"sym": sym, "bytes": limbs * 8}
    else:
        declaration = (
            "extern void %s(uint64_t *, const uint64_t *, const uint64_t *);" % sym
        )
        calls = """
    %(sym)s(separate, a, b);
    fiat_reference(reference, a, b);
    if (memcmp(separate, reference, %(bytes)d) != 0) return 3;
    memcpy(inplace1, a, sizeof(a));
    %(sym)s(inplace1, inplace1, b);
    if (memcmp(separate, inplace1, %(bytes)d) != 0) return 1;
    memcpy(inplace2, b, sizeof(b));
    %(sym)s(inplace2, a, inplace2);
    if (memcmp(separate, inplace2, %(bytes)d) != 0) return 2;
""" % {"sym": sym, "bytes": limbs * 8}
    return """#include <stdint.h>
#include <string.h>
#define %(reference_symbol)s fiat_reference
#include "%(reference)s"
#undef %(reference_symbol)s
%(declaration)s

int main(void) {
  uint64_t a[9], b[9], reference[9], separate[9], inplace1[9], inplace2[9];
  for (uint64_t trial = 0; trial < 8; trial++) {
    for (uint64_t i = 0; i < 9; i++) {
      a[i] = 0x101 + 0x111 * i + 0x1001 * trial;
      b[i] = 0x202 + 0x121 * i + 0x2003 * trial;
    }
%(calls)s
  }
  return 0;
}
""" % {
        "sym": sym,
        "reference_symbol": reference_symbol(sym),
        "reference": reference,
        "declaration": declaration,
        "calls": calls,
    }


def check(path, temporary_root):
    relative = path.relative_to(ROOT)
    work = temporary_root / (path.parent.name + "-" + path.stem)
    work.mkdir()
    asm = work / "implementation.s"
    harness = work / "harness.c"
    obj = work / "implementation.o"
    executable = work / "test"
    sym = symbol(path)
    op = operation(path)
    asm.write_text(gas_source(path))
    harness.write_text(
        harness_source(sym, op, limb_count(path), reference_path(path).as_posix())
    )
    try:
        subprocess.run(
            [CC, "-c", str(asm), "-o", str(obj)],
            check=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        subprocess.run(
            [CC, "-O2", str(harness), str(obj), "-o", str(executable)],
            check=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        result = subprocess.run(
            [str(executable)], stdout=subprocess.PIPE, stderr=subprocess.PIPE
        )
    except subprocess.CalledProcessError as error:
        detail = error.stderr.decode(errors="replace").strip()
        return relative, "build failed: " + detail
    if result.returncode == 0:
        return relative, None
    aliases = {
        1: "out1 == arg1",
        2: "out1 == arg2",
        3: "non-aliased result differs from fiat-c",
    }
    detail = aliases.get(result.returncode, "signal/exit %d" % result.returncode)
    return relative, "differs for " + detail


def main():
    if platform.machine().lower() not in ("x86_64", "amd64"):
        print("error: the AMD64 aliasing test requires an x86-64 host", file=sys.stderr)
        return 2
    if shutil.which(CC) is None:
        print("error: compiler not found: %s" % CC, file=sys.stderr)
        return 2
    paths = sorted(ASM_ROOT.glob("fiat_*/*.asm"))
    with tempfile.TemporaryDirectory(prefix="fiat-amd64-aliasing-") as temporary:
        temporary_root = Path(temporary)
        workers = min(8, os.cpu_count() or 1)
        with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as executor:
            results = list(
                executor.map(lambda path: check(path, temporary_root), paths)
            )
    failures = [(path, detail) for path, detail in results if detail is not None]
    for path, detail in failures:
        print("FAIL: %s: %s" % (path, detail))
    if failures:
        print("%d of %d assembly files failed" % (len(failures), len(paths)))
        return 1
    print("All %d assembly files support output/input aliasing" % len(paths))
    return 0


if __name__ == "__main__":
    sys.exit(main())
