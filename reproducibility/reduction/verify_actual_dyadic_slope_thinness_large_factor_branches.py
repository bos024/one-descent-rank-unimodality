"""Additional independent nonbulk QA. Wrap the frozen fourteen-report verifier."""
from pathlib import Path
from fractions import Fraction as Q
from collections import Counter
import json,hashlib,sys,time
ROOT=Path(__file__).resolve().parent
SOURCE=Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from verify_binary_ternary_A2_original_family import boxes
def at(A,n):return A[n] if 0<=n<len(A) else 0
def main():
    start=time.monotonic();oldpath=ROOT/'actual_dyadic_slope_thinness_verification.json'
    out=json.loads(oldpath.read_text(encoding='utf8'))
    assert out['status']=='PASS_UNBOUNDED_ACTUAL_DYADIC_SLOPE_THINNESS_AND_ALL_KAPPA_TWENTY_PLUS_MIXED_CLOSED_S'
    for n,d in out['sha256'].items():
        p=(ROOT if n in out['local_files'] else SOURCE)/n
        assert hashlib.sha256(p.read_bytes()).hexdigest()==d,n
    ct=Counter();rho=Q(3,5);b=Q(35,32);offset=Q(125,22);sha=hashlib.sha256()
    for K in [20,21,25,40]:
      for kind in ['last_capacity','initial_interval']:
        beta=1 if kind=='last_capacity' else 40*K
        V=list(range(2,K))
        if kind=='last_capacity':V[-1]+=40*K
        F=boxes(beta,V);M=beta+sum(t-1 for t in V);B=max([beta]+[t-1 for t in V]);O=M-B;S=min(M//2,O)
        assert O==S and O>=154
        if kind=='last_capacity':
            prefix=boxes(beta,V[:-1]);assert beta+sum(t-1 for t in V[:-1])==O
            value=sum(x*rho**n for n,x in enumerate(prefix));assert value+offset<=10*b**O
        else:
            zero=boxes(0,V);assert sum(t-1 for t in V)==O
            value=sum(x*rho**n for n,x in enumerate(zero));assert value+offset<=10*b**O
        for m in range(O+1,(M-1)//2+1):
            assert M>2*m
            d=at(F,m)-at(F,m-1)
            if kind=='last_capacity':
                assert d==at(prefix,m-1)-at(prefix,m-V[-1]-1)<=at(prefix,m-1)
                ct['independent_NONBULK_last_capacity_exact_difference_reads']+=1
            else:
                assert d<=at(zero,m)
                ct['independent_NONBULK_largest_initial_zero_seed_reads']+=1
            assert m*d<=1<<m
            if d>0:ct['independent_NONBULK_POSITIVE_signed_slopes']+=1
        ct['independent_NONBULK_genuine_large_factor_profiles']+=1
        sha.update(repr((K,kind,beta,V,F,S)).encode())
    assert ct['independent_NONBULK_last_capacity_exact_difference_reads']>0
    assert ct['independent_NONBULK_largest_initial_zero_seed_reads']>0
    assert ct['independent_NONBULK_POSITIVE_signed_slopes']>0
    extra=[oldpath.name,'verify_actual_dyadic_slope_thinness_large_factor_branches.py']
    out['local_files'] += extra
    out['sha256'].update({n:hashlib.sha256((ROOT/n).read_bytes()).hexdigest() for n in extra})
    out['independent_NONBULK_branch_QA']=dict(ct)
    out['independent_NONBULK_state_sha256']=sha.hexdigest()
    out['additional_branch_scope']='BOTH genuine NONBULK branches M>2m are independently checked: exact last-capacity derivative and zero-initial-run comparison for a largest initial interval. Positive signed slopes included. QA ONLY, no new theorem premise or additional kernel report.'
    out['additional_branch_seconds']=time.monotonic()-start
    (ROOT/'actual_dyadic_slope_thinness_full_branch_verification.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps(dict(status=out['status'],new_scoped_reports=out['new_scoped_reports'],independent_NONBULK_branch_QA=dict(ct),seconds=time.monotonic()-start)),flush=True)
if __name__=='__main__':main()
