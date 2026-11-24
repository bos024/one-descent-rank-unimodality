"""Exact word sets and all decreasing thresholds in two independently bounded domains."""
from collections import Counter
from itertools import combinations_with_replacement,product
from hashlib import sha256
from pathlib import Path
import json
from audit_depth_slack_bridge import fast_greedy,UI
def compositions(n):
    if not n:
        yield ()
    for x in range(1,n+1):
        for rest in compositions(n-x):yield (x,)+rest
def literal(host):
    words={()}
    for b in host:
        words|={v+(x,) for v in words for x in range(1,b+1)}
    return words
def main():
    ct=Counter();sha=sha256()
    for total in range(15):
        for w in compositions(total):
            signs=[(a<b)-(a>b) for a,b in zip(w,w[1:])]
            single=signs.count(-1)<=1
            bitonic=not any(j==1 and -1 in signs[:i] for i,j in enumerate(signs))
            if not(single or bitonic):continue
            indep=literal(w);c=Counter(map(sum,indep));row=[c[i] for i in range(total+1)]
            assert row==fast_greedy(w) and UI(row)
            ct['distinct_hosts']+=1
            ct['one_descent_or_monotone']+=single;ct['bitonic']+=bitonic
            ct['both_classes']+=single and bitonic
            ct['genuine_rank_coefficients']+=len(row);ct['distinct_word_memberships']+=len(indep)
            sha.update(repr((w,row)).encode())
    for h in range(5):
        for raw in combinations_with_replacement(range(1,5),h):
            caps=raw[::-1];pairs=[(0,0)]
            for ell in range(1,h+1):
                pairs.extend((sum(p),ell) for p in product(*(range(1,b+1) for b in caps[:ell])))
            hist=Counter(pairs)
            for n in range(1,min(sum(caps)+3,9)):
                ca=sum(v for (k,j),v in hist.items() if k<n)
                cb=sum(v for (k,j),v in hist.items() if k<=n)
                # All up-sets of (length, unused weight): each is a decreasing
                # list of thresholds, where n+1 represents "never".
                for asc in combinations_with_replacement(range(n+2),h+1):
                    t=asc[::-1]
                    a=sum(v for (k,j),v in hist.items() if k<n and n-1-k>=t[j])
                    b=sum(v for (k,j),v in hist.items() if k<=n and n-k>=t[j])
                    assert a*cb<=b*ca
                    ct['exact_joint_upper_sets']+=1
                L=sum(v for (k,j),v in hist.items() if k<=n and n-k>=(caps+(0,))[j])
                assert 2*cb-L==sum(v for (k,j),v in hist.items() if k<=n+1)
    data=dict(status='PASS_LITERAL_HOSTS_AND_ALL_JOINT_UPPER_SETS',max_host_weight=14,counts=dict(ct),digest=sha.hexdigest())
    print(data,flush=True)
    Path(__file__).with_name('literal_principal_ideals_audit.json').write_text(json.dumps(data,indent=2)+'\n',encoding='utf8')
if __name__=='__main__':main()