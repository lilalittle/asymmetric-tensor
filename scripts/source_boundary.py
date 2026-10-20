"""Explicit author-upload boundary shared by production inventories.

Only versioned single-file uploads directly inside AsymmetricTensor/ are drafts.
Spaces alone do not make a file a draft (Lean supports escaped module names).
"""
from pathlib import Path
import re

AUTHOR_DRAFT = re.compile(r"AsymmetricTensor/Asymmetric Tensor v[0-9]+(?:\.[0-9]+)*\.lean\Z")


def is_author_draft(relative):
    return AUTHOR_DRAFT.fullmatch(Path(relative).as_posix()) is not None


def author_drafts(root):
    return sorted(path for path in (root / "AsymmetricTensor").glob("*.lean")
                  if is_author_draft(path.relative_to(root)))


def production_sources(root):
    return [root / "AsymmetricTensor.lean", *sorted(
        path for path in (root / "AsymmetricTensor").rglob("*.lean")
        if not is_author_draft(path.relative_to(root)))]
