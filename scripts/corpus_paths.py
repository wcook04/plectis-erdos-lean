# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Locate corpus files through Lake's source roots, keeping module names stable.

Portable stdlib owner: ai_workflow/tools/meta/formal_math/corpus_paths.py.
The public scripts/corpus_paths.py is an exact copy. Historical root layouts
remain readable; current paths come from lakefile.toml, never from receipt age.
"""
from __future__ import annotations

from functools import lru_cache
from pathlib import Path
import tomllib
import re


@lru_cache(maxsize=32)
def _config(path: str, mtime_ns: int, size: int) -> dict:
    with Path(path).open('rb') as handle:
        return tomllib.load(handle)


def source_root(root: Path | str, library: str) -> Path:
    """Lake package srcDir followed by the selected lean_lib's srcDir.

    A new generated family inherits the existing families' common source root.
    An absent Lake config is the historical root layout used by small fixtures.
    Ambiguous family roots and paths escaping the checkout fail before writes.
    """
    root = Path(root)
    path = root / 'lakefile.toml'
    if not path.is_file():
        return root
    stat = path.stat()
    config = _config(str(path.resolve()), stat.st_mtime_ns, stat.st_size)
    libraries = config.get('lean_lib', [])
    exact = [row for row in libraries if row.get('name') == library]
    if exact:
        rows = exact[-1:]
    elif library.startswith('ExternalVerification'):
        rows = [row for row in libraries if row.get('name', '').startswith('ExternalVerification')]
    elif library in {'Solutions', 'PalomarCorpus'}:
        rows = [row for row in libraries if row.get('name') in {'Solutions', 'PalomarCorpus'}]
    else:
        rows = []
    roots = {str(row.get('srcDir', '.')) for row in rows} or {'.'}
    if len(roots) != 1:
        raise ValueError(f'ambiguous source roots for {library}: {sorted(roots)}')
    result = root / config.get('srcDir', '.') / roots.pop()
    if not result.resolve().is_relative_to(root.resolve()):
        raise ValueError(f'Lake source root for {library} escapes the checkout')
    return result


def corpus_path(root: Path | str, relative: Path | str) -> Path:
    """Resolve an old logical corpus path using this checkout's Lake config."""
    root, relative = Path(root), Path(relative)
    if relative.is_absolute() or '..' in relative.parts:
        raise ValueError(f'expected a repository-relative corpus path: {relative}')
    if not relative.parts:
        return root
    library = relative.parts[0]
    if library in {'Solutions', 'PalomarCorpus'} or library.startswith('ExternalVerification'):
        return source_root(root, library) / relative
    return root / relative


def relative_path(root: Path | str, relative: Path | str) -> str:
    return corpus_path(root, relative).relative_to(root).as_posix()


def family_entries(root: Path | str) -> list[Path]:
    return sorted(path for path in source_root(root, 'ExternalVerification').glob('ExternalVerification*') if path.is_dir())


def relocate_live_text(text: str, root: Path | str) -> str:
    """Refresh inline clone-local paths, excluding URLs and already nested paths."""
    pattern = r'(?<![\w/])((?:ExternalVerification[0-9][A-Za-z_0-9]*|PalomarCorpus|Solutions)/[A-Za-z_0-9./<>-]+)'
    return re.sub(pattern, lambda match: relative_path(root, match[1]), text)
