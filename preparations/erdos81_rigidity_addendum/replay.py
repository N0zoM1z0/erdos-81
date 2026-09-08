"""Dependency-free replay of saved exact finite partition/duality certificates."""
from pathlib import Path
from itertools import combinations
import json
from construct import verify_partition, certify_near_extremizer
root=Path(__file__).resolve().parent

def check_size_guard():
    """Negative control: a K4 is not a valid order-at-most-three partition."""
    E=set(combinations(range(4),2))
    try:
        verify_partition(E,[(0,1,2,3)],max_size=3)
    except AssertionError:
        return
    raise AssertionError('The partition verifier accepted an oversized block')

check_size_guard()
certs=json.loads((root/'partition_certificates.json').read_text())
checks=0
for c in certs:
    p,q=c['p'],c['q']; n=p+q
    E={tuple(e) for e in c['edges']}
    parts=[tuple(Q) for Q in c['parts']]
    a=len(c['missing']);m=len(c['outside']);cap=c['max_size']
    assert cap in (3,4)
    assert verify_partition(E,parts,max_size=cap)==c['value']
    assert a+2*m<=min(p,q-p)
    w={tuple(e[:2]):e[2] for e in c['dual_weights']}
    assert set(w)==E and sum(w.values())==c['value']
    for (x,y),z in w.items():
        assert z==(-1 if y<p else (-2 if cap==4 else -1) if x>=p else 1)
    # Universal clique-type dual inequalities: no clique search is needed.
    for x in range(p+1):
        for y in range(q+1):
            if x+y<2 or (cap==3 and x+y>3):continue
            val=x*y-x*(x-1)//2-(2 if cap==4 else 1)*y*(y-1)//2
            assert val<=1
            checks+=1
    if cap==4 and n>=100:
        deficit=n*(n+1)//6-c['value']
        if 0<=deficit<=n//100:
            r=certify_near_extremizer(n,E,deficit)
            assert r is not None and r['cp']==c['value']
            assert r['root']==list(range(p))
report={'verdict':'PASS','partition_certificates':len(certs),
        'negative_size_guard_checks':1,'clique_type_checks':checks}
(root/'replay_report.json').write_text(json.dumps(report,indent=2))
print(json.dumps(report,indent=2))
