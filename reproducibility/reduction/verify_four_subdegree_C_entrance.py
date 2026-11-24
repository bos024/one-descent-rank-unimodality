"""Independent positive-box verification of CI-count growth and the h=u+4 C entrance."""
from pathlib import Path
from itertools import accumulate
from random import Random
from collections import Counter
import json,hashlib,sys
from verify_double_subdegree_CI_entrance import multiplicities
from verify_subdegree_CI_entrance import suffix_boxes
from verify_divided_CI_surplus_three_primitive import kernel
ROOT=Path(__file__).resolve().parent
NAMES=['differential_product_identity','interval_differential_coefficients','loss_growth_seed_cone',
       'homogeneous_reference_ratio','earliest_ordinary_seed_identity','earliest_ordinary_seed_paid',
       'middle_ordinary_seed_identity','middle_ordinary_seed_paid','last_ordinary_seed_paid']

def conv(a,b):
    c=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):c[i+j]+=x*y
    return c

def main():
    qa=json.loads((ROOT/'audit_four_subdegree_C_entrance.json').read_text(encoding='utf8'))
    assert qa['status']=='EXACT_QA_FOUR_SUBDEGREE_ACTUAL_LATE_C_UNDER_AUDIT'
    ct=Counter();sha=hashlib.sha256();contexts=[]
    for h in range(5,15):
        for V in multiplicities(h,h):contexts.append((h-4,V))
    rng=Random(202610291241)
    for _ in range(100):
        V=sorted(rng.choices(range(3,21),k=rng.randint(1,9)));u=sum(t-1 for t in V)-4
        if u>=0:contexts.append((u,V))
    for u,V in contexts:
        h=u+4;r=len(V);W=h+r;w=u+r
        R=suffix_boxes(h+2,[2]*(h+1)+V);x=R[W]-R[W-1];y=R[W+1]-R[W];A=x*x+x*y-y*y
        assert R[W-3]<=y-x+1 and [R[W-2],R[W-1],R[W]]==[x-1,y,x+y] and A>0
        E=[1]
        for t in V+[2]*u:E=conv(E,[1]*t)
        for j in range(1,len(E)):
            assert j*E[j]>=(w-j+1)*E[j-1];ct['independent_CI_count_source_growth_margins']+=1
        for alpha in {1,2,3,4,5,u+h+3}:
            F=suffix_boxes(alpha,[2]*u+V);G=list(accumulate(F));raw=[1]+[F[n]-F[n-1] for n in range(1,len(F))];D=[max(0,z) for z in raw]
            losses=[(R[W-2+j]-R[W-3+j])-raw[W-2+j] for j in range(4)];a,l,b,c=losses;S=a+l;e=1+a
            assert F[W-3]==R[W-3] and F[W-2]==x-e and F[W-1]==y-S and F[W]==x+y-S-b
            if w>=11:
                assert l>=w*a and 2*b>=(w-1)*l and 3*c>=(w-2)*b
                assert S>=e and b>=2*S and b>=2*e+3 and c>=3*b and x>=2*w+3>=S and 2*y>=3*x
                assert F[W-1]*raw[W]-F[W-2]*raw[W+1]>=2*e*e
                assert F[W]*raw[W]-F[W-1]*raw[W+1]>0
                if raw[W+1]>=0:assert F[W-2]*raw[W]-F[W-3]*raw[W+1]>0
                ct['independent_three_ordinary_seed_instances']+=1
            if D[W+1]>D[W]>0:
                for k in range(1,W+1):assert G[k]*D[W]>=G[k-1]*D[W+1];ct['independent_all_prefix_boundary_seeds']+=1
            best=1
            for N in range(4,len(F)):
                k=N-3
                if G[k]*G[best-1]<G[best]*G[k-1]:best=k
                if N<W+1:continue
                assert G[best]*D[N-1]>=G[best-1]*D[N];ct['independent_all_shift_C_minimum_payments']+=1
                if u<=18 and r<=3:
                    for k in range(1,N-2):assert G[k]*D[N-1]>=G[k-1]*D[N];ct['independent_literal_C_products']+=1
            sha.update(json.dumps([u,V,alpha,F],separators=(',',':')).encode());ct['independent_actual_hosts']+=1
        ct['independent_CI_profiles']+=1
    if '--reconstruct-only' in sys.argv:
        print(json.dumps(dict(status='PASS_INDEPENDENT_FOUR_SUBDEGREE_ACTUAL_C',counts=dict(ct),state_sha256=sha.hexdigest())),flush=True);return
    kernels={'FourSubdegreeCEntrance':kernel('FourSubdegreeCEntrance',NAMES)}
    deps=['triple_subdegree_C_entrance_verification.json','two_factor_complete_entrance_verification.json',
          'automatic_late_C_cones_verification.json','homogeneous_reference_and_sharp_entrance_verification.json',
          'multitail_binary_prefix_finite_principle_verification.json']
    for path in deps:
        dep=json.loads((ROOT/path).read_text(encoding='utf8'))
        for name,digest in dep['sha256'].items():assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest()==digest,name
    files=['four_subdegree_C_entrance_proof.tex','FourSubdegreeCEntrance.lean','FourSubdegreeCEntrance.log',
           'audit_four_subdegree_C_entrance.py','audit_four_subdegree_C_entrance.json',
           'verify_four_subdegree_C_entrance.py','homogeneous_reference_complete_C.tex']+deps
    out=dict(status='PASS_UNBOUNDED_FOUR_SUBDEGREE_ALL_PADDING_ACTUAL_LATE_C',new_scoped_reports=9,kernels=kernels,
        state_sha256=qa['state_sha256'],QA=qa['counts'],independent_counts=dict(ct),independent_state_sha256=sha.hexdigest(),new_finite_entrance_certificates=0,
        CI_count_growth='PROVED EVERY actual CI-binomial E=(1+z)^u prod[t], t>=3, factorcountw=u+r: (1+z)Eprime-wE is coefficientwiseNONNEGATIVE. ANY nonnegative multiplicative formal power series N preserves this cone. Thus ENTIRE finite-binary+initial-ones loss L=E*(H2+z^(alpha-1)) satisfies jLj>=(w-j+1)Lprev. Replacing u by w REQUIRES actual interval factors; not asserted for arbitrary LC numerators.',
        reference_ratio='PROVED EVERY reference with W+r>=8 has Dref(W+1)>=3Dref(W)/2. Old whole-word norm gives t<=q^(W+r-2)<=q6=5-8q, y/x=(phi-qt)/(1+t). Complete scalar ratio implication kernel checked; unbounded spectral assembly written. Also x>=Fib(W-1)>=2w+3 at W=w+4,w>=11.',
        entrance='PROVED ALL w>=11: first four losses yield e=1+l0,S=l0+l1,b=l2,c=l3 with S>=e,b>=2S,b>=2e+3,c>=3b,x>=max(S,2e). Three EXACT ordinary seeds pay successive F reads W-2/W-1/W, INCLUDING reference F(W-2)=x-1. Earliest reference F(W-3)<=y-x+1 uses NONNEGATIVE numerator B(W-1), not false homogeneous extrapolation. Growing-pair ratio<phi, unchanged G throughW-3, universal late-D-LC and integration pay every later C read.',
        actual='PROVED EVERY sorted1^alpha2^uV, h=u+4, ALLcapacities/counts/paddings,EVERYshift>=3 at EVERYN>=W+1. w<11 hasW<=14 and uses OLD weight32 complete-C theorem. NO NEW FINITE ENTRANCE OR EXCEPTION CERTIFICATE.',
        threshold='ALL actual late C NOW u>=h-4, allparametersunbounded; oldu>=h-3 plusNEW h=u+4.',
        formal_scope='NINE new scoped standard-axiom kernel reports:interval/product differential identities,complete loss seed cone,reference ratio,and all three seed identities/payments. Coefficientwise product/series, Fibonacci bound, old whole-word norm, actual source/reference and integration assemblies WRITTEN, not end-to-end Lean composition theorem. ALL finite profiles are QA ONLY.',
        remaining='Potential actual LATE-C failures now requireu>=9,u+5<=h<=3u-2,maxcap<=2u-1,W>32. Earlier actual/reference C, general C/A2/original UI remain OPEN; first original unresolved full-C nonone count6 unchanged.',
        general_original='OPEN',general_C='OPEN',general_A2='OPEN',actual_late_C_threshold='u>=h-4',
        sha256={f:hashlib.sha256((ROOT/f).read_bytes()).hexdigest() for f in files})
    (ROOT/'four_subdegree_C_entrance_verification.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if k!='sha256'}),flush=True)

if __name__=='__main__':main()
