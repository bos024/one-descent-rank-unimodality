"""Exact small tests of the two initial ranges in the strict-peak proof (Python 3.10+)."""
from collections import Counter
from functools import lru_cache
from hashlib import sha256
from itertools import combinations_with_replacement
import json

def increasing(weight, least=1):
    if weight==0:
        yield ()
    for head in range(least,weight+1):
        for tail in increasing(weight-head,head):
            yield (head,)+tail

@lru_cache(maxsize=75000)
def words(host):
    """Classify nonempty words by their first letter and its earliest possible position."""
    if not host:
        return (1,)
    result=[1]+[0]*sum(host)
    previous_max=0
    for position,cap in enumerate(host):
        if cap>previous_max:
            for letter in range(previous_max+1,cap+1):
                for degree,count in enumerate(words(host[position+1:])):
                    result[letter+degree]+=count
            previous_max=cap
    return tuple(result)

def product(p,q):
    result=[0]*(len(p)+len(q)-1)
    for i,first in enumerate(p):
        for j,second in enumerate(q):
            result[i+j]+=first*second
    return result

def at(p,index):
    return p[index] if 0<=index<len(p) else 0

def one_change(differences):
    fell=False
    for change in differences:
        if fell and change>0:
            return False
        fell|=change<0
    return True

def review():
    counts=Counter()
    result_hash=sha256()
    arms=[w for a in range(1,11) for w in increasing(a) if w[0]==1 and w[-1]>1]
    for X,Y in combinations_with_replacement(arms,2):
        a,b=sum(X),sum(Y)
        assert a<=b
        A,B=words(X),words(Y)
        P=product(A,B)
        p=P[::-1]
        for peak in [*range(max(X[-1],Y[-1])+1,b+2),b+4]:
            if b-a>peak-4:
                continue
            N=a+b+peak
            subtotal=0
            core=[]
            for n in range(N+1):
                subtotal+=at(P,n-1)-at(P,n-1-peak)
                core.append(at(A,n)+at(B,n)+subtotal-at(P,n))
            assert tuple(core)==words(X+(peak,)+Y)==words(X+(peak,)+Y[::-1])
            reverse=core[::-1]
            end=N//2
            dw=[at(p,n)-2*at(p,n-peak)+at(p,n-peak-1) for n in range(end+1)]
            assert dw==[at(reverse,n)-at(reverse,n-1) for n in range(end+1)]
            assert all(dw[n]==at(p,n)>=0 for n in range(min(peak,end+1)))
            assert one_change(dw[:max(b,peak)]) and one_change(dw)
            for poly in (core,[c-at(B,i) for i,c in enumerate(core)],[c-at(A,i) for i,c in enumerate(core)]):
                assert one_change(c-at(poly,i-1) for i,c in enumerate(poly))
            counts['heavier_arm_below_peak' if b<peak else
                   'heavier_arm_equal_to_peak' if b==peak else 'heavier_arm_above_peak']+=1
            counts['strict_peak_instances']+=1
            counts['reverse_half_edges']+=len(dw)
            result_hash.update(repr((X,Y,peak,tuple(core),tuple(dw))).encode('ascii'))
    assert all(counts[k] for k in ('heavier_arm_below_peak','heavier_arm_equal_to_peak','heavier_arm_above_peak'))
    return dict(status='PASS_EXACT_STRICT_PEAK_JOIN_BOUNDARIES',maximum_arm_weight=10,
                counts=dict(counts),sha256=result_hash.hexdigest())

if __name__=='__main__':
    if not __debug__:
        raise SystemExit('Run without Python optimization so that assertions are enabled.')
    print(json.dumps(review(),sort_keys=True))
