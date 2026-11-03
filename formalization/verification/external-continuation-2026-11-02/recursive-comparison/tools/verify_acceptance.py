#!/usr/bin/env python3
"""Read-only technical acceptance, reconstructed 2026-11-02; never invokes Lean.
Requires prospective freeze, successful direct compiler receipts, exact gate
closure snapshots and actual namespace audit logs. Semantic source review is
separate. Failure writes a rejected report, never silently relaxes a check.
"""
import argparse, datetime, hashlib, json, pathlib, re, subprocess
from capture_freeze import digest, within, module_name, canonical

ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}

def uncomment(s):
    out=[]; i=0; depth=0
    while i<len(s):
        if s.startswith('/-',i): depth+=1; i+=2
        elif depth and s.startswith('-/',i): depth-=1; i+=2
        elif not depth and s.startswith('--',i):
            j=s.find('\n',i); i=len(s) if j<0 else j
        else:
            out.append(s[i] if not depth or s[i]=='\n' else ' '); i+=1
    return ''.join(out)

def validate(a):
    root=a.repo.resolve(); freeze=json.loads(a.freeze.read_text())
    baseline=json.loads(a.baseline.read_text()); before=json.loads(a.before.read_text()); after=json.loads(a.after.read_text())
    assert freeze['phase']=='before-candidate-authoring' and freeze['schema']=='author-freeze-v2'
    assert set(freeze['allowed_axioms'])==ALLOWED
    assert all(e['exists'] is False for e in freeze['candidate_files'])
    for group in ['frozen_files','source']:
        for row in freeze[group]:
            assert digest(within(root,row['path']))==row['sha256'], 'Frozen source changed: '+row['path']
    assert before==after, 'Closure changed during compiler gate'
    clone=dict(before); expected=clone.pop('closure_sha256')
    assert hashlib.sha256(json.dumps(clone,sort_keys=True,separators=(',',':')).encode()).hexdigest()==expected
    for path,sha in before['bindings'].items(): assert digest(within(root,path))==sha, 'Binding changed: '+path
    for row in before['files']: assert digest(within(root,row['path']))==row['sha256'], 'Closure stale: '+row['path']
    gate_entry=next(e for e in freeze['frozen_files'] if e['role']=='gate'); gate=module_name(gate_entry['path'])
    allowed_requests={gate}|{module_name(e['path']) for e in freeze['candidate_files']}
    assert gate in before['requested'] and set(before['requested'])<=allowed_requests, 'Snapshot must select the frozen gate and only declared candidates'
    # Independently recompute current import closure using the pinned local snapshot implementation.
    fresh=a.output.with_suffix('.recomputed-closure.json')
    assert not fresh.exists(), 'Refusing overwrite of independent closure evidence'
    snap=pathlib.Path(__file__).with_name('snapshot_closure.py')
    subprocess.run(['python3',str(snap),'--repo',str(root),'--output',str(fresh),*before['requested']],check=True,capture_output=True)
    assert json.loads(fresh.read_text())==before, 'Current closure differs from gate snapshot'
    # Baseline is an explicit Git-source index, not an assertion of fresh compilation.
    assert baseline['schema']=='git-baseline-source-index-v1'
    audit='formalization/LogicLineages/Audit.lean'
    assert digest(within(root,audit))==baseline['files'][audit], 'Audit implementation changed'
    declared={e['path'] for e in freeze['frozen_files']}|{e['path'] for e in freeze['candidate_files']}
    changed=[r for r in before['files'] if baseline['files'].get(r['path'])!=r['sha256']]
    assert {r['path'] for r in changed}<=declared, 'Unfrozen extra local source in gate closure'
    for r in changed:
        text=uncomment(within(root,r['path']).read_text())
        assert not re.search(r'\b(sorry|admit|native_decide|axiom|unsafe)\b',text), 'Forbidden construct: '+r['path']
    receipts=[a.receipt,*a.extra_receipt]
    comparator=pathlib.Path(freeze['comparator_receipt'])
    assert digest(comparator)==freeze['comparator_receipt_sha256']
    receipts.append(comparator); rows={}; receipt_evidence=[]
    for p in receipts:
        doc=json.loads(p.read_text())
        assert doc['modules'] and all(r['returncode']==0 for r in doc['modules']), 'Failed receipt: '+str(p)
        assert doc.get('upstream_cache_only') is True and doc.get('threads')==1
        receipt_evidence.append({'path':str(p),'sha256':digest(p)})
        for row in doc['modules']: rows[row['module']]=row
    closure={r['module']:r for r in before['files']}
    for row in changed:
        assert row['module'] in rows, 'New source lacks successful direct compiler row: '+row['module']
        assert rows[row['module']]['source_sha256']==row['sha256'], 'Direct source hash mismatch'
    assert gate in rows and rows[gate]['source_sha256']==gate_entry['sha256']
    gate_log=within(root,'formalization/'+rows[gate]['log']); text=gate_log.read_text()
    assert not re.search(r'\berror:|forbidden axiom dependency',text), 'Gate log errors'
    actual={}; audits={}
    for match in re.finditer(r'AXIOMS ([^\s:]+): \[([^\]]*)\]',text):
        name,values=match.groups(); axioms=[x.strip() for x in values.split(',') if x.strip()]
        assert set(axioms)<=ALLOWED, 'Forbidden axiom: '+name
        assert name not in actual, 'Duplicate gate audit row: '+name
        actual[name]=axioms
    for match in re.finditer(r'AXIOM_AUDIT_PASS ([^\s:]+): (\d+) theorems',text): audits[match[1]]=int(match[2])
    assert actual and audits, 'Missing actual axiom audit output'
    gate_text=uncomment(within(root,gate_entry['path']).read_text())
    for alias in freeze['aliases']:
        short=alias['declaration'].rsplit('.',1)[-1]
        assert re.search(r'\btheorem\s+'+re.escape(short)+r'\s*:\s*'+re.escape(alias['target'])+r'\s*:=',gate_text)
        assert alias['declaration'] in actual, 'Exact alias absent from actual audit'
        ns=alias['namespace']; assert ns in audits
        assert sum(n==ns or n.startswith(ns+'.') for n in actual)==audits[ns], 'Namespace audit count mismatch'
    return {'schema':'independent-acceptance-v2','status':'verified-technical-evidence','errors':[],
        'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'freeze_sha256':digest(a.freeze),'baseline_sha256':digest(a.baseline),
        'baseline_commit':baseline['commit'],'gate':gate,'aliases':freeze['aliases'],
        'accepted_scope':freeze['scope'],'source_review':freeze['root_review_reference'],
        'new_changed_sources':changed,'receipts':receipt_evidence,
        'before_sha256':digest(a.before),'after_sha256':digest(a.after),'closure_sha256':expected,
        'gate_log_sha256':digest(gate_log),'actual_axiom_rows':actual,'namespace_audits':audits,
        'validator_sha256':digest(pathlib.Path(__file__)),'snapshot_script_sha256':digest(snap),
        'limitations':['Technical verification does not independently establish manuscript semantics.',
                      'Compilation uses the recorded pinned warm cache; no clean-room or CI pass claimed.']}

def main():
    p=argparse.ArgumentParser(description=__doc__)
    for name in ['repo','freeze','receipt','before','after','baseline','output']:
        p.add_argument('--'+name,required=True,type=pathlib.Path)
    p.add_argument('--extra-receipt',action='append',default=[],type=pathlib.Path)
    a=p.parse_args(); assert not a.output.exists(), 'Acceptance output already exists'
    try: result=validate(a)
    except Exception as e:
        result={'schema':'independent-acceptance-v2','status':'rejected','errors':[str(e)],'exception':type(e).__name__}
    a.output.parent.mkdir(parents=True,exist_ok=True)
    with a.output.open('xb') as f: f.write(canonical(result))
    print(json.dumps({'status':result['status'],'errors':result['errors'],'path':str(a.output)}))
    raise SystemExit(0 if result['status']=='verified-technical-evidence' else 1)

if __name__=='__main__':main()
