"""Lexical helpers for source auditing; Lean remains authoritative for types/axioms.

Comment/string masking adapts the original development's MIT-licensed checker.
"""
import re
from pathlib import Path
import tomllib


def proof_snapshot(root, config='comparator.json'):
    """Identity of all Lean sources and the pinned build/comparison inputs."""
    import hashlib
    paths = set(sources(root))
    paths.update(root / name for name in
                 ['lean-toolchain', 'lakefile.toml', 'lakefile.lean',
                  'lake-manifest.json', config] if (root / name).is_file())
    return {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in sorted(paths)}


def snapshot_digest(snapshot):
    import hashlib
    import json
    return hashlib.sha256(json.dumps(snapshot, sort_keys=True,
                                     separators=(',', ':')).encode()).hexdigest()

DECL = re.compile(
    r'^\s*(?:@\[[^\]]*\]\s*)?'
    r'(?P<mods>(?:(?:public|private|protected|noncomputable|unsafe|partial)\s+)*)'
    r'(?P<kind>theorem|lemma|def|abbrev|opaque|structure|inductive|class|axiom|constant|instance)'
    r'\s+(?P<name>[^\s(:{]+)')


def mask(source):
    out, i, depth, string = list(source), 0, 0, False
    while i < len(source):
        if depth:
            if source.startswith('/-', i):
                out[i:i + 2] = '  '; depth += 1; i += 2
            elif source.startswith('-/', i):
                out[i:i + 2] = '  '; depth -= 1; i += 2
            else:
                if source[i] != '\n': out[i] = ' '
                i += 1
        elif string:
            if source[i] == '\\' and i + 1 < len(source):
                out[i:i + 2] = '  '; i += 2
            else:
                if source[i] == '"': string = False
                if source[i] != '\n': out[i] = ' '
                i += 1
        elif source.startswith('/-', i):
            out[i:i + 2] = '  '; depth = 1; i += 2
        elif source.startswith('--', i):
            j = source.find('\n', i)
            j = len(source) if j < 0 else j
            out[i:j] = ' ' * (j - i); i = j
        elif source[i] == '"':
            out[i] = ' '; string = True; i += 1
        else:
            i += 1
    return ''.join(out)


def imports(source):
    """Read ordinary module imports, including public/meta/import-all modifiers."""
    return re.findall(r'^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?(\S+)',
                      mask(source), re.MULTILINE)


def sources(root):
    """All submitted sources, excluding .git/.lake; include links to reject them."""
    import os
    result = []
    for directory, dirs, files in os.walk(root, followlinks=False):
        dirs[:] = sorted(d for d in dirs if d not in {'.git', '.lake'}
                         and not (Path(directory) / d).is_symlink())
        result.extend(Path(directory) / f for f in sorted(files) if f.endswith('.lean'))
    return result


def submitted_files(root):
    """Regular source-tree files without descending into caches or Git state."""
    import os
    result = []
    for directory, dirs, files in os.walk(root, followlinks=False):
        dirs[:] = sorted(d for d in dirs if d not in {'.git', '.lake', '__pycache__'}
                         and not (Path(directory) / d).is_symlink())
        result.extend(p for f in sorted(files) if (p := Path(directory) / f).is_file()
                      and not p.is_symlink())
    return result


def source_roots(root):
    """Ordered actual source roots for this declarative flattened project."""
    configs = [root / 'lakefile.toml']
    roots = {root}
    for config in configs:
        data = tomllib.loads(config.read_text())
        package_root = config.parent
        base = package_root / data.get('srcDir', '.')
        roots.add(base.resolve())
        for library in data.get('lean_lib', []):
            roots.add((package_root / library.get('srcDir', data.get('srcDir', '.'))).resolve())
        for requirement in data.get('require', []):
            if 'path' in requirement:
                config = (package_root / requirement['path'] / 'lakefile.toml').resolve()
                if config not in configs: configs.append(config)
    return sorted(roots, key=lambda p: len(p.parts), reverse=True)


def module_for_source(path, roots):
    for base in roots:
        if path.is_relative_to(base):
            return '.'.join(path.relative_to(base).with_suffix('').parts)
    raise ValueError(f'cannot resolve source root for {path}')


def scan(paths, root):
    declarations, violations = [], []
    for path in sorted(paths):
        source, scopes = mask(path.read_text(encoding='utf-8')), []
        for match in re.finditer(r'\b(?:sorry|admit|sorryAx|native_decide|Lean\.ofReduceBool)\b', source):
            violations.append({'file': str(path.relative_to(root)),
                               'line': source.count('\n', 0, match.start()) + 1,
                               'token': match.group()})
        for lineno, line in enumerate(source.splitlines(), 1):
            ns = re.match(r'\s*namespace\s+([\w.]+)\s*$', line)
            sec = re.match(r'\s*(?:(?:public|noncomputable)\s+)?section(?:\s+([\w.]+))?\s*$', line)
            end = re.match(r'\s*end(?:\s+([\w.]+))?\s*$', line)
            if ns: scopes.append(('namespace', ns[1])); continue
            if sec: scopes.append(('section', sec[1] or '')); continue
            if end:
                if scopes: scopes.pop()
                continue
            match = DECL.match(line)
            if not match: continue
            if match['kind'] in {'axiom', 'constant'}:
                violations.append({'file': str(path.relative_to(root)), 'line': lineno,
                                   'token': match['kind']})
            if {'unsafe', 'partial'} & set(match['mods'].split()):
                violations.append({'file': str(path.relative_to(root)), 'line': lineno,
                                   'token': match['mods'].strip()})
            if 'private' in match['mods'].split(): continue
            name = match['name']
            prefix = '.'.join(s for kind, s in scopes if kind == 'namespace')
            name = name.removeprefix('_root_.') if name.startswith('_root_.') else \
                '.'.join(s for s in [prefix, name] if s)
            declarations.append({'name': name, 'kind': match['kind'],
                                 'file': str(path.relative_to(root)), 'line': lineno})
    return declarations, violations
