"""Review navigation from actual elaborated declaration dependencies.

An edge means a claim's bound declarations use a declaration also bound by a
second claim. It does not assert that either English claim has been accepted.
"""
from collections import deque

def claim_connections(claims, declarations):
    bindings = {c['id']: {b['lean'] for b in c['cleanroom_mapping']['bindings']}
                for c in claims if c['cleanroom_mapping']}
    result = {cid: {'uses': [], 'used_by': [], 'shared': []} for cid in bindings}
    for cid, roots in bindings.items():
        paths = {n: [n] for n in sorted(roots)}
        queue = deque(paths)
        while queue:
            node = queue.popleft()
            for dep in declarations.get(node, {}).get('dependencies', []):
                if dep in declarations and dep not in paths:
                    paths[dep] = paths[node] + [dep]
                    queue.append(dep)
        for other, targets in bindings.items():
            if other == cid:
                continue
            shared = roots & targets
            if shared:
                result[cid]['shared'].append({'claim': other, 'declarations': sorted(shared)})
                continue
            candidates = [paths[n] for n in targets if n in paths]
            if candidates:
                path = min(candidates, key=lambda p: (len(p), p))
                result[cid]['uses'].append({'claim': other, 'path': path})
                result[other]['used_by'].append({'claim': cid, 'path': path})
    return result
