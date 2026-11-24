"""Exact QA of a new physical boundary; all profiles QA, no finite entrance premise."""
from pathlib import Path
import sys,json,time,hashlib
from math import comb
from itertools import accumulate
from random import Random
from collections import Counter
ROOT=Path(__file__).resolve().parent
SOURCE=ROOT if (ROOT/'audit_joint_structure.py').exists() else Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from audit_minimum_staircase_scaled_dyadic import arm_prefix
from audit_degree_boundary_CI_entrance import ci
from audit_binary_CI_infinite_padding_entrance import binary
from audit_joint_structure import fastconv
from audit_arbitrary_Fibonacci_tail_late_C import sign,add,sub,mul,power
from audit_homogeneous_reference_and_sharp_entrance import rebuild,c_minimum
Q=(-1,1);PHI=(0,1);PSI=(1,-1);ONE=(1,0);ZERO=(0,0)

def val(A,n):return A[n] if 0<=n<len(A) else 0
def csum(A,n):return sum(A[:max(0,n+1)])

def main():
    start=time.monotonic();rng=Random(20261031205);ct=Counter();sha=hashlib.sha256();profiles=[]
    for t in range(3,26):
        for r in range(1,6):
            V=[t]*r;h=(t-1)*r
            for u in {0,1,max(0,h-4),h-2,h-1,h,h+3,2*h}:profiles.append((u,V))
    for _ in range(380):
        V=sorted(rng.choices(range(3,31),k=rng.randint(1,12)));h=sum(t-1 for t in V)
        profiles.append((rng.randint(0,2*h),V))
    for u,V in profiles:
        r=len(V);h=sum(t-1 for t in V);W=h+r;w=u+r;delta=h-u;L=ci(V);C=fastconv(L,binary(u-1)) if u else [0]
        E=fastconv(L,[comb(u,j) for j in range(u+1)]);Inf=arm_prefix(W+2,[2]*u+V,W+1)
        P=1
        for t in V:P*=t
        assert Inf[W]==P+csum(C,h-2) and Inf[W-1]==P-1+csum(C,h-3) and Inf[W-2]==P-r-1+csum(C,h-4)
        a,b=Inf[W-1]-Inf[W-2],Inf[W]-Inf[W-1]
        assert a==val(C,h-3)+r and b==val(C,h-2)+1;ct['exact_previous_r_units_and_current_unit_identities']+=1
        rho=ONE
        for t in V:rho=mul(rho,mul(Q,sub(ONE,power(PSI,t))))
        atom=mul(power(PHI,2),rho);gap=(-b,a)
        if delta>=2:
            if not u:assert (a,b)==(r,1);ct['zero_binary_boundary_payments']+=1
            else:
                n=delta-2;f=ZERO
                for j in range(n+1):f=sub((E[j],0),mul(Q,f))
                assert gap==sub(add(PHI,f),atom);ct['exact_boundary_quotient_plus_phi_identities']+=1
                if h<=3*u+2:
                    if not n:assert sign(gap)>0 and gap==mul(power(PHI,2),sub(ONE,rho));ct['two_degree_gap_positive_payments']+=1
                    else:
                        assert E[n]>=w>=2 and sign(sub(f,mul(power(Q,2),(E[n],0))))>=0
                        assert sign(sub((2,0),atom))>=0 and sign(sub(gap,power(Q,2)))>=0
                        ct['unbounded_monotone_CI_head_payments']+=1
                else:
                    assert val(C,h-3)>=val(C,h-2) and a>=b>0;ct['large_degree_symmetric_row_payments']+=1
        else:
            assert gap==sub(PHI,atom);ct['protected_reference_boundary_gap_identities']+=1
            if r>=2:assert sign(sub(gap,power(Q,5)))>=0;ct['multiple_factor_norm_payments']+=1
            else:
                expected=power(Q,V[0]-1)
                if V[0]%2:expected=(-expected[0],-expected[1])
                assert gap==expected;ct['sharp_one_factor_parity_controls']+=1
        exception=r==1 and V[0]%2 and delta<=1
        assert (sign(gap)<0)==bool(exception)
        R=rebuild(V,W+1);Gref=list(accumulate(R));rd=[0,0]+[R[n]-R[n-1] for n in range(2,len(R))]
        assert (-rd[W],rd[W-1])==sub(PHI,atom)
        for k in range(1,W-2):
            assert sign(sub((Gref[k],0),mul(PHI,(Gref[k-1],0))))>0
            assert Gref[k]*rd[W-1]>=Gref[k-1]*rd[W];ct['all_shift_reference_boundary_C_products']+=1
        for alpha in {1,2,max(1,delta+1),rng.randint(1,h+u+5)}:
            F=arm_prefix(alpha,[2]*u+V,alpha+2*u+W+1);G=list(accumulate(F));D=[0,0]+[max(0,F[n]-F[n-1]) for n in range(2,len(F))]
            assert D[W]*a<=D[W-1]*b;ct['finite_padding_boundary_density_transfers']+=1
            if exception:assert D[W-1]>0 and sign((-D[W],D[W-1]))<0;ct['all_padding_protected_odd_counteredges']+=1
            elif D[W-1]:assert sign((-D[W],D[W-1]))>0;ct['all_padding_boundary_golden_payments']+=1
            else:assert D[W]==0
            maxk=min(W-3,w+1)
            for k in range(1,maxk+1):
                assert G[k]*D[W-1]>=G[k-1]*D[W];ct['actual_new_boundary_large_shift_C_products']+=1
            if u>=h-4:
                assert maxk==W-3
                c_minimum(F,D,W,len(F)-1,ct)
                ct['all_padding_earlier_full_C_halfline_hosts']+=1
            ct['actual_hosts']+=1
        sha.update(json.dumps([u,V,a,b,gap,rho],separators=(',',':')).encode());ct['CI_profiles']+=1
    F=arm_prefix(3,[2]*46+[12,18,20],51);D=[F[n]-F[n-1] for n in (49,50,51)];minor=D[1]**2-D[0]*D[2]
    assert D==[20296909601,32841089600,53137999199] and minor<0 and sign((-D[1],D[0]))>0
    out=dict(status='EXACT_QA_PHYSICAL_BOUNDARY_GOLDEN_D_AND_EARLIER_C_UNDER_AUDIT',counts=dict(ct),state_sha256=sha.hexdigest(),seconds=time.monotonic()-start,
        actual_D_LC_earlier_start_counter=dict(alpha=3,u=46,V=[12,18,20],centre=50,D=D,minor=minor),
        scope='Written universal physicalW golden D edge with exactly old onefactor odd-capacity protected exceptions; ALL actual boundaryC shiftsR>=max(3,h-u-1); ALLu>=h-4 actual everyC startsW insteadW+1; ALLnonbinary infinite-binary reference everyC startsW. No finite entrance premise. D-LC itself does NOT start one earlier. General earlierC/fullA2/originalUI OPEN.')
    (ROOT/'audit_physical_boundary_golden_C.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)

if __name__=='__main__':main()
