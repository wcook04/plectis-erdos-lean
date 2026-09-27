# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Explicit legacy release membership, independent of Lake computation defaults.

Palomar has its own publication enumeration. Auxiliary directory discovery is
not admission to this inventory. Missing selection never means source-only.
"""
import json
from pathlib import Path
import re
import tomllib

NAME = re.compile(r"[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*\Z")


def selection(root: Path) -> dict:
    path = root / 'release-entries.json'
    if not path.is_file():
        raise ValueError('Missing release-entries.json: restore the reviewed release population; build focus cannot waive release obligations')
    value = json.loads(path.read_text())
    if not isinstance(value, dict) or value.get('schema') != 'plectis_release_selection_v1':
        raise ValueError('Unsupported release selection schema; source-only artifacts cannot qualify a release')
    for field in ('entries', 'support_targets'):
        rows = value.get(field)
        if not isinstance(rows, list) or any(not isinstance(x, str) or not NAME.fullmatch(x) for x in rows):
            raise ValueError(f'release-entries.json {field} must be an array of module/library names')
        if len(rows) != len(set(rows)):
            raise ValueError(f'Duplicate release selection in {field}')
    if not value['entries']:
        raise ValueError('Empty release population: restore reviewed entries; narrowing build defaults is not a release exemption')
    if any(not re.fullmatch(r'ExternalVerification[0-9]+[A-Za-z_0-9]*', x) for x in value['entries']):
        raise ValueError('Legacy release entries must be ExternalVerification packages; Palomar is a separate population')
    if set(value['entries']) & set(value['support_targets']):
        raise ValueError('Duplicate release target across entries and support_targets')
    libraries = {row['name'] for row in tomllib.loads((root/'lakefile.toml').read_text()).get('lean_lib', [])}
    missing = set(value['entries'] + value['support_targets']) - libraries
    if missing:
        raise ValueError('Release targets missing Lake library declarations: ' + ', '.join(sorted(missing)))
    return value


def entries(root: Path) -> list[str]:
    return sorted(selection(root)['entries'])


def build_targets(root: Path) -> list[str]:
    declared = selection(root)
    return declared['entries'] + declared['support_targets']


def validate_workflow_contract(root: Path) -> str:
    """Admit both deployed legacy drivers and the shared release driver.

    Old drivers consume defaultTargets. Until they are migrated, defaults must
    contain every release obligation. This check never changes membership.
    """
    workflow = root / '.github/workflows/release-gate.yml'
    if not workflow.is_file():
        raise ValueError('Missing release gate workflow; source-only artifacts cannot qualify a release')
    gate = workflow.read_text()
    if 'uses: ./.github/workflows/lean.yml' in gate:
        driver = (root/'.github/workflows/lean.yml').read_text()
        if driver.count('if [[ "$AUDIT_PUBLICATION" == true ]]; then args+=(--release); fi') != 2 or 'audit_publication: true' not in gate:
            raise ValueError('Shared release driver must select --release for both plan and compile before its audit')
        return 'shared_release_inventory'
    if 'defaultTargets' in gate and 'subprocess.run(["lake", "build", target]' in gate:
        defaults = tomllib.loads((root/'lakefile.toml').read_text()).get('defaultTargets', [])
        missing = set(build_targets(root)) - set(defaults)
        if missing:
            raise ValueError('Legacy release workflow would omit required builds: '+', '.join(sorted(missing))+
                             '. Preserve package defaults and use an explicit focused command, or adopt the shared --release driver.')
        return 'legacy_complete_defaults'
    raise ValueError('Unrecognised release execution contract; review the driver before publication')
