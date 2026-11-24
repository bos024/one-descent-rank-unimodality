"""Independent positive-box models and direct signed polynomial coefficient checks."""
from pathlib import Path
from random import Random
from collections import Counter
import sys,json,time,re,hashlib
ROOT=Path(__file__).resolve().parent
SOURCE=Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from verify_binary_ternary_A2_original_family import boxes,conv,UI
def at(p,n):return p[n] if 0<=n<len(p) else 0
def prefixconv(p,q,N):return [sum(at(p,i)*at(q,n-i) for i in range(n+1)) for n in range(N+1)]
def win(p,t):return [sum(at(p,n-j) for j in range(t)) for n in range(len(p)+t-1)]
def checkC(F,ct):
    G=[];s=0
    for x in F+[0,0,0]:s+=x;G.append(s)
    D=[0,0]+[max(0,at(F,n)-at(F,n-1)) for n in range(2,len(G))]
    m=1
    for n in range(4,len(G)):
        k=n-3
        if G[k]*G[m-1]<G[m]*G[k-1]:m=k
        assert G[m]*D[n-1]>=G[m-1]*D[n]
        ct['independent_actual_FULL_C_currents']+=1
def main():
    st=time.monotonic();ct=Counter();rng=Random(9731043);sha=hashlib.sha256()
    for _ in range(350):
        k=rng.randint(6,75);delta=rng.randint(0,k)
        U=[rng.randint(0,20) for _ in range(rng.randint(1,12))];U[0]+=1;A=[1,1,2]+U
        Q=[1]+[2**(i-1) for i in range(1,k)]+[2**(k-1)-delta,rng.randint(1,25),rng.randint(1,25)]
        Q += [-rng.randint(1,20) for _ in range(10)]
        H=prefixconv(A,Q,k+2)
        dQ=[x-at(Q,i-1) for i,x in enumerate(Q)]
        for n in range(k,k+3):
            tail=sum(at(A,i)*at(dQ,n-i) for i in range(3,len(A)))
            assert H[n]-H[n-1]==Q[n]+Q[n-2]-2*Q[n-3]+tail>0
            ct['independent_generic_complete_polynomial_slope_identities']+=1
    for k in range(6,31):
        for j in range(5):
            V=([k-1]*(k-2) if j%2==0 else list(range(2,k)))
            beta=1+j;Y=boxes(beta,V)
            X=boxes(1+j,sorted(rng.randint(2,18) for _ in range(1+j*2)))
            H=conv(X,Y);D=len(H)-1
            assert UI(H) and all(H[n]>H[n-1] for n in [k,k+1,k+2])
            mu=H.index(max(H));assert mu>=k+2 and D-mu<=D-k-2
            ct['independent_actual_product_mode_bounds']+=1
            sha.update(str((X,Y,H[k-1:k+3],mu)).encode())
    for k in range(6,46):
        opposite=[(2,[k-1]*(k-1)),(k,[k+1]*(k-2)),(1,list(range(2,k)))]
        for beta,V in opposite:
            Y=boxes(beta,V);b=len(Y)-1;checkC(Y,ct)
            assert next(n for n in range(1,k+1) if at(Y,n)<2**(n-1))==k
            delta=2**(k-1)-Y[k];assert 1<=delta<=k
            for alpha,s in [(1,2),(2,2),(2,4),(4,5)]:
                X=boxes(alpha,[s]);a=len(X)-1;p=conv(X[::-1],Y[::-1])
                E=[2*at(p,n)-at(p,n-1) for n in range(len(p)+2)]
                d=[max(0,x-at(p,n-1)) for n,x in enumerate(p)];assert UI([x<<n for n,x in enumerate(d)])
                if a+3<=k:
                    L=b+a-k+1;m=min(alpha+1,s);R=b+m-1
                    assert E[L]==delta and UI(E[:L+1]) and min(E[:L+1])>=1
                    assert E[L+1:b]==[0]*(b-1-L) and E[b:R+1]==[1]*m
                    assert max(E[R+1:],default=0)<=0
                    assert len(p)-1-p[::-1].index(max(p))<=L-3
                    ct['independent_unbounded_entire_one_part_profiles']+=1
                else:assert UI([max(0,x) for x in E])
                for t in [k-3,k+1,b+1]:
                    W=[max(0,x) for x in win(E,t)];assert UI(W)
                    pos=[n for n,x in enumerate(W) if x>0];assert pos==list(range(pos[-1]+1))
                    ct['independent_entire_one_part_window_repairs']+=1
    for k in range(6,71):
        X=boxes(1,[2]);Y=boxes(1,[k-1]*(k-2));b=len(Y)-1
        assert 2**(k-1)-Y[k]==3
        p=conv(X[::-1],Y[::-1]);E=[2*at(p,n)-at(p,n-1) for n in range(len(p)+2)]
        assert win(E,k-4)[b-1:b+2]==[3,1,2]
        ct['independent_actual_unbounded_shorter_window_obstructions']+=1
        # Separate synthetic full patch profiles explicitly meet the UI-prefix hypothesis.
        L=b+4-k;S=[2]+[3]*L+[0]*(k-5)+[1,1]+[-1,0,-1]
        assert UI(S[:L+1]) and win(S,k-4)[b-1:b+2]==[3,1,2]
        ct['independent_abstract_patch_threshold_obstructions']+=1
    src=(ROOT/'FirstMissingProductMode.lean').read_text(encoding='utf8')
    log=(ROOT/'FirstMissingProductMode.log').read_text(encoding='utf8')
    assert not any(x in src for x in ['native_decide','sorry','axiom '])
    assert not any(x in log for x in ['warning:','error:','sorryAx','ofReduceBool','failed'])
    rows=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",log,re.S);assert len(rows)==10
    kernels={n:[x.strip() for x in v.split(',') if x.strip()] for n,v in rows}
    assert all(set(a)<={'propext','Classical.choice','Quot.sound'} for a in kernels.values())
    local=['first_missing_product_mode_and_one_part_window_proof.tex','FirstMissingProductMode.lean','FirstMissingProductMode.log',
        'audit_first_missing_product_mode.py','audit_first_missing_product_mode.json','verify_first_missing_product_mode.py']
    deps=['first_missing_hooks.tex','FirstMissingHooks.lean','FirstMissingHooks.log','audit_first_missing_hooks.py','audit_first_missing_hooks.json',
        'ordinary_rooted_caterpillar_model.tex','kappa_eight_original_window_criterion_verification.json',
        'kappa_eight_legal_window_original_criterion_proof.tex','kappa_seven_original_window_criterion_verification.json',
        'GeneralFiniteSourcePatch.lean','GeneralFiniteSourcePatch.log','KappaSixWindowRepair.lean','KappaSixWindowRepair.log',
        'binary_ternary_A2_original_family_verification.json','binary_ternary_A2_original_family_proof.tex',
        'C_to_coupled_S_rising_window.tex','agent_bothdeclining_first_birth.tex','agent_half_lc_actual_weak_curvature.tex',
        'source_birth_gap_nonrecovery.tex','signed_kernel_extension.tex','verify_binary_ternary_A2_original_family.py']
    for name in [n for n in deps if n.endswith('_verification.json')]:
        dep=json.loads((SOURCE/name).read_text(encoding='utf8'))
        for n,digest in dep['sha256'].items():assert hashlib.sha256((SOURCE/n).read_bytes()).hexdigest()==digest,(name,n)
    primary=json.loads((ROOT/'audit_first_missing_product_mode.json').read_text(encoding='utf8'))
    assert primary['status']=='PASS_EXACT_QA_FIRST_MISSING_PRODUCT_MODE_AND_UNBOUNDED_ONE_PART_WINDOWS'
    out=dict(status='PASS_UNBOUNDED_FIRST_MISSING_PRODUCT_MODE_AND_CONDITIONAL_ONE_PART_SOURCE_WINDOWS',
        new_scoped_reports=10,kernels=kernels,
        product_mode='ANYACTUALnonrectX/Y,kappaY>=6:ordinaryH=FXFYstrictlyincreasesatrankskappa,kappa+1,kappa+2. FIRSTordinarymode>=kappa+2/LASTreverseproductmode<=a+b-kappa-2. NO_C/NO_A2/NOmodehypothesis,ALLparametersunbounded.',
        whole_polynomial='A=1+z+2z2+z3U,U>=0/U0>=1;QfullDYADICprefixbelowkappa/firstdefectdelta<=kappa/positiveatnextTHREEranks. WHOLEprotectedD-Qprefix/finiteconvolutionpositive/constantpayment/exactslopeidentity=>ALLTHREEincreases. SubsequentQcoefficientsneedNOTbenonnegative. NOsampledsourcepositivitypremise.',
        one_part_windows='ANYactualX=1alpha_s_ONEpart/YnonrectFULLC,assumingFULL_OLD_PAIR_A2:ENTIRE([t](2-z)qXqY)^+UI/initialsupportforallt>=max(1,kappaY-3),UNBOUNDEDkappaY. FULL_OLD_A2premiseRETAINED. Generalh>=2ownerwindowcriterionOPEN.',
        complete_profile='OnlyonepartQbirthfailurea+3<=kappa. ExactWHOLEsource:positiveINTEGERUIprefix0..L,L=b+a-kappa+1,endpointdelta;ZEROSL+1..b-1;ONESb..R=b+min(alpha+1,s)-1;NONPOSafterR. NEWmodeboundnu<=L-3;body>=1;R-L<=kappa-3 givesFROZENgenericpatch. ALLindices/birthdichotomyunboundedkernelchecked.',
        obstruction='EVERYkappa>=6 ACTUALX1/2,Y1/(kappa-1)^(kappa-2)hasEXACTdelta3(ONLYTHREEmissinghooks)andwindowt=kappa-4triple3,1,2. C/FULL_A2forENTIREunboundedcounterfamilyNOTasserted. AbstractUIprefix(2,3,..3)+samecriticalprofileALSOviolatesshorterwindow,sohypothesesofgenericpatchcannotimprovelength.',
        formal_scope='TENnewstandardaxiomreportsincludeWHOLEpolynomialthree-increaseproof/exactcompleteidentity/protectedderivativeprefix/completeconvolutionandconstantpayment/powbudget/modeimplication/unboundedonepartgeometryandbirthdichotomy. Actualhookbound/model/unimodality/C-A1-Q andFROZENgenericwindowassemblyWRITTEN,NOTendtoendLeancompositions. NOfiniteproofpremise. OnepartsourcewindowresultCONDITIONALonFULL_OLD_A2;NOgeneralsolutioninferred.',
        new_finite_proof_premises=0,general_original='OPEN',general_C='OPEN',general_A2='OPEN',
        independent_counts=dict(ct),primary_QA=primary['counts'],independent_state_sha256=sha.hexdigest(),seconds=time.monotonic()-st,
        local_files=local,dependency_files=deps,
        sha256={n:hashlib.sha256(((ROOT if n in local else SOURCE)/n).read_bytes()).hexdigest() for n in local+deps})
    (ROOT/'first_missing_product_mode_verification.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if k not in ['kernels','sha256','local_files','dependency_files']}),flush=True)
if __name__=='__main__':main()
