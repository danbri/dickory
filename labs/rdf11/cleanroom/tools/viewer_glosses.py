"""Attach reviewable English explanations to declarations, with explicit provenance.

Authored declarations require a curated gloss. Compiler-generated declarations
are explained by their role and their nearest documented parent, never silently
presented as independent spec claims. Glosses are not kernel-checked translations.
"""
import json
import re

def attach_glosses(lean, catalogue, root):
    source = json.loads((root / 'catalogue/lean-glosses.json').read_text())['declarations']
    rows = lean['declarations']
    missing = []
    for name,row in rows.items():
        if name in source:
            text = source[name]
            kind = 'Authored English gloss'
        else:
            # Compiler range metadata also points constructors/fields to fragments
            # of their parent's declaration. They are not standalone definitions.
            code = row.get('code','').lstrip()
            inherited = any(name.startswith(p+'.') and code == r.get('code','').lstrip() for p,r in rows.items() if p != name)
            without_comments = re.sub(r'/\-.*?\-/', '', code, flags=re.S)
            authored = bool(re.search(r'\b(abbrev|def|theorem|structure|inductive|instance)\b', without_comments)) and not inherited
            if authored:
                missing.append(name)
                continue
            candidates = [p for p in source if name.startswith(p+'.')]
            parent = max(candidates,key=len) if candidates else None
            tail = name[len(parent)+1:] if parent else name.rsplit('.',1)[-1]
            if row['kind']=='constructor':
                role = 'This constructor builds a value of '+(parent or row['module'])+' from the arguments shown in its type.'
            elif tail in {'rec','recOn','casesOn'} or 'match_' in tail or 'splitter' in tail:
                role = 'This compiler-generated case-analysis helper lets a proof or function handle the possible forms of a value.'
            elif 'sizeOf' in tail:
                role = 'This generated helper measures Lean values for termination machinery. It is not RDF graph cardinality.'
            elif '.eq_' in name or '.eq_def' in name:
                role = 'This generated equation records how the parent definition reduces on the indicated inputs.'
            elif 'noConfusion' in tail or '.inj' in name:
                role = 'This generated equality rule distinguishes constructors or recovers equality of their arguments.'
            elif parent:
                role = 'This field or generated helper belongs to '+parent+'. Its exact arguments and result appear under Elaborated type.'
            else:
                role = 'This generated support declaration supplies Lean machinery for '+row['module']+'. Its exact operation is given by the elaborated type; it is not an additional RDF assertion.'
            text = role + (' Parent definition: '+source[parent] if parent else '')
            kind = 'Generated-helper explanation'
        row['gloss']={'text':text,'note':kind+' · draft, awaiting expert review; explanatory prose is not checked by the Lean kernel.'}
    if missing:
        raise ValueError('Authored Lean declarations need English glosses: '+', '.join(missing))
    stale=set(source)-set(rows)
    if stale:
        raise ValueError('Gloss refers to absent declaration: '+', '.join(sorted(stale)))
