"""Exact QA of universal below-degree golden ceiling and local large-shift C/S."""
from pathlib import Path
import sys
ROOT=Path(__file__).resolve().parent
SOURCE=ROOT if (ROOT/'audit_joint_structure.py').exists() else Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from random import Random
from math import comb
from collections import Counter
from itertools import accumulate
import json,hashlib,time
from audit_degree_boundary_CI_entrance import ci
from audit_joint_structure import fastconv
from audit_minimum_staircase_scaled_dyadic import arm_prefix
from audit_homogeneous_reference_and_sharp_entrance import rebuild
from verify_degree_boundary_CI_entrance import reverse_divided
from audit_arbitrary_Fibonacci_tail_late_C import sign,sub,mul,power,evaluate
Q=(-1,1);PSI=(1,-1);P=(0,1);Z=(0,0)

def main():
    rng=Random(20261031141);ct=Counter();sha=hashlib.sha256();start=time.monotonic()
    for trial in range(900):
        V=sorted(rng.choices(range(3,28),k=rng.randint(1,12)));r=len(V);h=sum(t-1 for t in V);u=rng.randint(1,h-1)
        delta=h-u;W=h+r;w=u+r;L=ci(V);J=reverse_divided(L,u);E=fastconv(L,[comb(u,i) for i in range(u+1)])
        c=mul(power(PSI,u),evaluate(L,(0,-1)));n=delta-1
        assert sign(c)==(-1)**delta and sign(mul(c,power(PSI,n)))<0;ct['exact_helpful_entry_parity_checks']+=1
        Inf=arm_prefix(delta+1,[2]*u+V,W+1);inf0=Inf[W]-Inf[W-1];inf1=Inf[W+1]-Inf[W]
        assert J[n]==(-inf1,inf0);ct['actual_previous_unit_and_inverse_entry_identities']+=1
        if h<=3*u+2:
            f=Z
            for j in range(n+1):
                f=sub((E[j],0),mul(Q,f))
                assert sign(f)>0 and sign(sub((E[j],0),f))>=0 and sign(sub(f,mul(sub((1,0),Q),(E[j],0))))>=0
                if j:assert E[j]>=E[j-1]
                ct['complete_monotone_division_head_reads']+=1
            assert sign(J[n])>0;ct['positive_natural_quotient_entries']+=1
        else:assert inf1<=inf0;ct['automatic_nonincreasing_reference_entries']+=1
        R=rebuild(V,w+1);gref=list(accumulate(R))
        for alpha in {1,2,delta+1,rng.randint(3,u+h+3)}:
            F=arm_prefix(alpha,[2]*u+V,alpha+2*u+W+3);G=list(accumulate(F));D=[0,0]+[max(0,F[i]-F[i-1]) for i in range(2,len(F))]
            assert F[:w+2]==R[:w+2]
            if D[W]>0:
                assert D[W+1]*inf0<=D[W]*inf1;ct['actual_finite_padding_density_entry_comparisons']+=1
            best=1;mins=[0]*(w+2)
            for k in range(1,w+2):
                if G[k]*G[best-1]<G[best]*G[k-1]:best=k
                mins[k]=best
            for N in range(W+1,len(F)):
                if D[N-1]>0:
                    assert sign((-D[N],D[N-1]))>0;ct['entire_actual_positive_tail_golden_ceiling_checks']+=1
                else:assert D[N]==0
                kmax=min(w+1,N-3)
                if kmax>=1:
                    k=mins[kmax];assert G[k]*D[N-1]>=G[k-1]*D[N];ct['large_shift_all_prefix_minimum_C_payments']+=1
                    ct['logical_large_shift_coverage']+=kmax
                    if trial<15:
                        for k in range(1,kmax+1):assert G[k]*D[N-1]>=G[k-1]*D[N];ct['literal_large_shift_C_products']+=1
            ct['actual_hosts']+=1
        outside=u>=9 and h>=u+5 and h<3*u-1 and max(V)<2*u and W>32 and 17*u+4*r+17<13*h
        ct['CI_profiles_outside_registered_full_late_C_families']+=outside
        sha.update(json.dumps([u,V,J[n],inf0,inf1],separators=(',',':')).encode());ct['CI_profiles']+=1
    # An actual local S witness outside every registered whole-owner late-C cone.
    u=20;V=[3]*20;alpha=21;beta=50;U=[19]*18;cwt=121;bwt=392;j=60;N=61;t=452;n=cwt+bwt-j;k=n-t
    A=arm_prefix(alpha,[2]*u+V,cwt);B=arm_prefix(beta,U,bwt);AB=fastconv(A,B);EB=[0,0]+[2*B[i-1]-B[i] for i in range(2,len(B))]
    kappa=next(i for i,z in enumerate(EB) if z);assert kappa==20
    assert A[N]>A[N-1] and B[N]>B[N-1] and all(EB[i]>=EB[i-1] for i in range(1,N+1))
    H=fastconv(EB,A);DA=[0,0]+[max(0,A[i]-A[i-1]) for i in range(2,len(A))]
    source_ratio_margin=H[N]*DA[j]-H[j]*DA[N];assert source_ratio_margin>=0
    cur=2*AB[j]-AB[N];prev=2*AB[j-1]-AB[j];assert cur>=0 and cur-prev>=0
    p=fastconv(A[::-1],B[::-1]);pos=[max(0,p[i]-(p[i-1] if i else 0)) for i in range(len(p))];weighted=[z*2**i for i,z in enumerate(pos)];ell=weighted.index(max(weighted))
    assert all(weighted[i]<=weighted[i+1] for i in range(ell)) and all(weighted[i]>=weighted[i+1] for i in range(ell,len(weighted)-1))
    assert k<cwt and n<cwt+t and k<ell and p.index(max(p))<n
    vn=p[n-1]-p[n];vn1=p[n]-p[n+1];S_margin=2*(pos[k+1]+vn1)-(pos[k]+vn);assert S_margin>=0
    new_raw_window_positive_difference=p[n]-p[k];assert new_raw_window_positive_difference>0
    witness=dict(owner_alpha=21,owner_u=20,owner_V=V,opposite_beta=50,opposite_V=U,current_forward_N=N,
        opposite_first_missing=kappa,source_overlap_depth=N-4-kappa,old_weights=[cwt,bwt],append_t=t,reverse_n=n,head_k=k,
        old_weighted_first_mode=ell,old_product_first_mode=p.index(max(p)),outside_owner_full_late_C_union=True,
        nonnegative_current_source=cur,source_nonrecovery_margin=cur-prev,source_ratio_margin=source_ratio_margin,S_margin=S_margin,
        new_raw_window_positive_difference=new_raw_window_positive_difference,
        scope='ONE finite actual correctly conditioned source/S witness. Generic theorem remains CONDITIONAL on nonnegative source/strict-rise/physical-head guards and OLD A2 head. Not a full A2 induction or original solution.')
    out=dict(status='EXACT_QA_UNIVERSAL_GOLDEN_TAIL_AND_LARGE_SHIFT_C_UNDER_AUDIT',counts=dict(ct),local_S_witness=witness,state_sha256=sha.hexdigest(),seconds=time.monotonic()-start,
        scope='Proposed UNBOUNDED allh>u actual tail phi ceiling and ALL h/u actual large-shift C at N>=W+1,N-R<=u+r+1. Both helpful spectral parity and actual previous unit retained; no full cumulative LC assumption. Local original S resource uses only the shifts actually read and retains OLD head/current guards. All finite checks QA ONLY; original C/A2/UI OPEN.')
    (ROOT/'audit_golden_tail_large_shift_C.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if k!='local_S_witness'}),flush=True)
    print(json.dumps({k:v for k,v in witness.items() if not k.endswith('margin') and k!='nonnegative_current_source'}),flush=True)

if __name__=='__main__':main()
