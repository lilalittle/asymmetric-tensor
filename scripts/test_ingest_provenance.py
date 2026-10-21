#!/usr/bin/env python3
"""Exercise author line provenance in real, temporary Git histories (no Lean build)."""
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest


AUTHOR = "Fixture Author"
STEWARD = "Fixture Steward"
AUTHORED = (
    "-- The authored balance identity is recorded in Equation (balnace).\n"
    "theorem authored_balance_identity (left right : Nat) : "
    "left + right = right + left := Nat.add_comm left right\n"
)
OTHER = (
    "theorem authored_nonnegative_square (value : Int) : "
    "0 <= value * value := Int.mul_self_nonneg value\n"
)
NOVEL = "-- Steward originated this independent migration coverage explanation.\n"


class ProvenanceTest(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="ingest-provenance-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.env = {key: value for key, value in os.environ.items()
                    if not key.startswith("GIT_")}
        self.env.update({"GIT_CONFIG_NOSYSTEM": "1", "GIT_CONFIG_GLOBAL": os.devnull})
        self.git("init", "-q")
        self.git("config", "core.autocrlf", "false")
        self.source = self.root / "author-v1.lean"
        self.source.write_text(AUTHORED + OTHER)
        self.author_commit = self.commit("Preserve exact author source", AUTHOR)
        self.author_blob = self.git("rev-parse", "HEAD:author-v1.lean").strip()

        # Copy two blocks without touching the immutable upload. The source is
        # not modified by this commit, so cross-file copy detection matters.
        (self.root / "Algebra.lean").write_text(AUTHORED)
        (self.root / "Bounds.lean").write_text(OTHER)
        self.split_commit = self.commit("Split authored content into modules", STEWARD)
        self.git("mv", "Algebra.lean", "Balance.lean")
        self.commit("Move balance module", STEWARD)

        self.target = self.root / "Balance.lean"
        self.target.write_text(AUTHORED.replace("identity is", "identity  is"))
        self.repair_commit = self.commit("Mechanical whitespace change only", STEWARD)
        # Only the mechanical repair is ignored; the new explanation is separate.
        (self.root / ".git-blame-ignore-revs").write_text(
            "# Reviewed whitespace change; no new mathematical content.\n"
            + self.repair_commit + "\n"
        )
        self.commit("Record reviewed mechanical revision", STEWARD)
        with self.target.open("a") as output:
            output.write(NOVEL)
        self.novel_commit = self.commit("Explain new migration coverage", STEWARD)

    def git(self, *args, env=None):
        return subprocess.run(
            ["git", *args], cwd=self.root, env=env or self.env,
            text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=True,
        ).stdout

    def commit(self, message, author):
        env = dict(self.env, GIT_AUTHOR_NAME=author,
                   GIT_AUTHOR_EMAIL=author.lower().replace(" ", "-") + "@example.invalid",
                   GIT_COMMITTER_NAME=STEWARD,
                   GIT_COMMITTER_EMAIL="fixture-steward@example.invalid")
        self.git("add", ".")
        self.git("-c", "commit.gpgsign=false", "commit", "-qm", message, env=env)
        return self.git("rev-parse", "HEAD").strip()

    def blame(self, filename, enhanced=True, ignore=True):
        args = ["-c", "blame.markIgnoredLines=true",
                "-c", "blame.markUnblamableLines=true", "blame", "--line-porcelain"]
        if enhanced:
            args += ["-w", "-M", "-C", "-C", "-C"]
            if ignore:
                args += ["--ignore-revs-file", ".git-blame-ignore-revs"]
        lines = self.git(*args, "HEAD", "--", filename).splitlines()
        records, record = [], {}
        for line in lines:
            if line.startswith("\t"):
                record["text"] = line[1:]
                records.append(record)
                record = {}
            elif not record:
                header = line.split()
                record["commit"] = header[0]
                record["original_line"] = int(header[1])
                record["final_line"] = int(header[2])
            else:
                key, _, value = line.partition(" ")
                record[key] = value
        return records

    def origin_text(self, line):
        source = self.git("show", line["commit"] + ":" + line["filename"])
        return source.splitlines()[line["original_line"] - 1]

    def test_preserved_source_and_copied_moved_lines(self):
        self.git("merge-base", "--is-ancestor", self.author_commit, "HEAD")
        self.assertEqual(self.source.read_text(), AUTHORED + OTHER)
        self.assertEqual(self.git("rev-parse", "HEAD:author-v1.lean").strip(),
                         self.author_blob)
        for filename, line_index, original_line in [
                ("Balance.lean", 1, 2), ("Bounds.lean", 0, 3)]:
            line = self.blame(filename)[line_index]
            self.assertEqual(line["commit"], self.author_commit)
            self.assertEqual(line["author"], AUTHOR)
            self.assertEqual(line["filename"], "author-v1.lean")
            self.assertEqual(line["committer"], STEWARD)
            self.assertEqual(line["original_line"], original_line)
            self.assertEqual(self.origin_text(line),
                             (AUTHORED + OTHER).splitlines()[original_line - 1])

    def test_mechanical_repair_recovers_author_origin(self):
        default = self.blame("Balance.lean", enhanced=False)[0]
        self.assertEqual(default["commit"], self.repair_commit)
        self.assertEqual(default["author"], STEWARD)
        for ignore in (False, True):
            with self.subTest(ignore=ignore):
                traced = self.blame("Balance.lean", ignore=ignore)[0]
                self.assertEqual(traced["text"],
                                 AUTHORED.splitlines()[0].replace("identity is", "identity  is"))
                self.assertEqual(traced["commit"], self.author_commit)
                self.assertEqual(traced["author"], AUTHOR)
                self.assertEqual(traced["filename"], "author-v1.lean")
                self.assertEqual(traced["original_line"], 1)
                self.assertEqual(self.origin_text(traced), AUTHORED.splitlines()[0])
                self.assertNotIn("unblamable", traced)

    def test_new_steward_content_is_not_reassigned(self):
        line = self.blame("Balance.lean")[-1]
        self.assertEqual(line["text"], NOVEL.rstrip("\n"))
        self.assertEqual(line["commit"], self.novel_commit)
        self.assertEqual(line["author"], STEWARD)
        self.assertEqual(line["filename"], "Balance.lean")
        self.assertEqual(line["original_line"], 3)
        self.assertEqual(self.origin_text(line), NOVEL.rstrip("\n"))
        self.assertNotIn("ignored", line)
        self.assertNotIn("unblamable", line)

    def test_reference_repair_reports_actual_trace_or_exception(self):
        before_text = self.target.read_text()
        self.assertEqual(before_text.count("balnace"), 1)
        self.target.write_text(before_text.replace("balnace", "balance"))
        reference_repair = self.commit("Repair reference spelling only", STEWARD)
        before = self.blame("Balance.lean", ignore=False)[0]
        self.assertEqual(before["commit"], reference_repair)
        self.assertEqual(before["author"], STEWARD)

        with (self.root / ".git-blame-ignore-revs").open("a") as output:
            output.write("# Reviewed reference spelling repair.\n" + reference_repair + "\n")
        self.commit("Record reference repair exclusion", STEWARD)
        after = self.blame("Balance.lean")[0]
        # Unlike whitespace, this repair cannot disappear merely because of -w.
        # Require evidence that ignoring the revision actually affected blame.
        self.assertTrue(after["commit"] != before["commit"] or "ignored" in after
                        or "unblamable" in after,
                        "Ignoring the reference repair had no observable effect")
        self.assertEqual(after["text"], before["text"])
        self.assertEqual(self.source.read_text(), AUTHORED + OTHER)
        self.assertEqual(self.git("rev-parse", "HEAD:author-v1.lean").strip(),
                         self.author_blob)
        self.git("merge-base", "--is-ancestor", self.author_commit, "HEAD")

        expected = {"commit": self.author_commit, "path": "author-v1.lean",
                    "line": 1, "text": AUTHORED.splitlines()[0], "author": AUTHOR}
        actual = {"commit": after["commit"], "path": after["filename"],
                  "line": after["original_line"], "text": self.origin_text(after),
                  "author": after["author"]}
        # A test pass means this audit ran, not that Git recovered the author.
        # Git versions may improve the trace; never require a particular failure.
        print("REFERENCE_REPAIR_TRACE: " + json.dumps({
            "outcome": "SUPPORTED_TRACE" if actual == expected else "EXCEPTION",
            "reported_origin": actual, "immutable_author_mapping": expected,
            "source_blob": self.author_blob,
        }, sort_keys=True))
        novel = self.blame("Balance.lean")[-1]
        self.assertEqual(novel["commit"], self.novel_commit)
        self.assertEqual(novel["author"], STEWARD)
        self.assertEqual(novel["filename"], "Balance.lean")
        self.assertEqual(novel["original_line"], 3)
        self.assertEqual(self.origin_text(novel), NOVEL.rstrip("\n"))


if __name__ == "__main__":
    unittest.main()
