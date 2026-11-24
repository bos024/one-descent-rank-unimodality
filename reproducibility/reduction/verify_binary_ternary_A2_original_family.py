"""Independent positive boxes and greedy deterministic composition-ideal counts.
Finite tests are QA only; no finite premise is used in the new universal proofs.
"""
from pathlib import Path
from collections import Counter
from random import Random
import sys,json,hashlib,re,time
ROOT=Path(__file__).resolve().parent
SOURCE=Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from verify_subdegree_CI_entrance import suffix_boxes

def conv(a,b):
    c=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):c[i+j]+=x*y
    return c
def at(p,n):return p[n] if 0<=n<len(p) else 0
def UI(p):
    k=p.index(max(p))
    return all(p[n]<=p[n+1] for n in range(k)) and all(p[n]>=p[n+1] for n in range(k,len(p)-1))
def boxes(a,U):return suffix_boxes(a,U)[:a+sum(U)+1]
def greedy_ideal(host):
    """Each composition follows its UNIQUE greedy leftmost embedding.
    States retain its last matched host position. No arm/core recurrence used.
    """
    L=len(host);N=sum(host);dp=[[0]*(N+1) for _ in range(L+1)];dp[0][0]=1
    for state in range(L):
        first={}
        for j in range(state,L):
            for x in range(1,host[j]+1):
                if x not in first:first[x]=j+1
        for x,target in first.items():
            for n,v in enumerate(dp[state][:-x]):
                if v:dp[target][n+x]+=v
    return [sum(dp[state][n] for state in range(L+1)) for n in range(N+1)]

def check(A,B,ct,sha,fullsource=True):
    p=conv(A[::-1],B[::-1]);E=[2*at(p,n)-at(p,n-1) for n in range(len(p)+2)]
    d=[max(0,x-at(p,n-1)) for n,x in enumerate(p)]
    assert UI([v*2**n for n,v in enumerate(d)])
    ct['independent_actual_FULL_A2_hosts']+=1
    if fullsource:
        assert UI([v*2**n for n,v in enumerate(p)])
        P=[max(0,e) for e in E];assert UI(P)
        support=[i for i,e in enumerate(E) if e>0];assert support==list(range(support[-1]+1))
        nu=max(i for i,x in enumerate(p) if x==max(p))
        a,b=len(A)-1,len(B)-1;D=a+b
        for n in range(nu+1,len(E)-1):
            if E[n]<0:continue
            assert E[n+1]<=E[n];ct['independent_Q_post_LAST_mode_edges']+=1
            j=D-n
            kind=(at(A,j+1)>at(A,j),at(B,j+1)>at(B,j))
            ct['independent_Q_forward_phase_'+str(kind)]+=1
        for t in [1,3,5,13,57]:
            W=[sum(at(E,n-i) for i in range(t)) for n in range(len(E)+t-1)]
            assert UI([max(0,w) for w in W]);ct['independent_ENTIRE_signed_windows']+=1
        ct['independent_ENTIRE_source_cone_hosts']+=1
    sha.update(str((A,B,p,d,E)).encode())

def core(A,B,M):
    C=conv(A,B);N=len(C)+M
    T=[sum(at(C,n-i) for i in range(1,M+1))-at(C,n) for n in range(N)]
    L=[v+at(A,n) for n,v in enumerate(T)]
    R=[v+at(B,n) for n,v in enumerate(T)]
    H=[v+at(B,n) for n,v in enumerate(L)]
    while H and H[-1]==0:H.pop();L.pop();R.pop()
    assert min(L)>=0 and min(R)>=0 and UI(L) and UI(R) and UI(H)
    return H,L,R

def kernel():
    s=(ROOT/'BinaryTernaryA2SourceCone.lean').read_text(encoding='utf8')
    log=(ROOT/'BinaryTernaryA2SourceCone.log').read_text(encoding='utf8')
    assert not any(x in log for x in ['warning:','error:','sorryAx','ofReduceBool','failed'])
    assert 'native_decide' not in s
    rows=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",log,re.S);assert len(rows)==10
    out={}
    for n,raw in rows:
        ax=[v.strip() for v in raw.split(',') if v.strip()]
        assert set(ax)<={'propext','Classical.choice','Quot.sound'};out[n]=ax
    return out

def main():
    st=time.monotonic();ct=Counter();sha=hashlib.sha256();rng=Random(2026110183)
    def profile(kind,small=False):
        a=rng.randint(1,8 if small else 80);cap=4 if small else 22
        if kind==0:U=[2]*rng.randint(0,cap)+[3]*rng.randint(0,cap)
        elif kind==1:U=[2]*rng.randint(0,cap)+[rng.randint(2,9 if small else 90)]
        else:U=sorted(rng.randint(2,9 if small else 80) for _ in range(rng.randint(0,2)))
        return a,U
    for case in range(720):
        a,U=profile(case%3);b,V=profile(case//3%3);A,B=boxes(a,U),boxes(b,V)
        for F,W in [(A,U),(B,V)]:
            if W:
                k=next(n for n in range(1,6) if at(F,n)<2**(n-1));assert 3<=k<=4
                ct['independent_A4_first_missing_controls']+=1
        check(A,B,ct,sha,bool(U and V))
        maximum=max([1]+U+V)
        for M in [maximum+1,maximum+7]:
            H,L,R=core(A,B,M);ct['independent_A4_ORIGINAL_cores']+=1;ct['independent_BOTH_relatives']+=2
            sha.update(str((M,H,L,R)).encode())
        t=max(max(U+[2]),len(B)-len(A),rng.randint(2,160))
        X=[1]+[sum(at(A,n-i) for i in range(t)) for n in range(len(A)+t-1)]
        check(X,B,ct,sha,False)
        H,L,R=core(X,B,max(maximum,t)+1);ct['independent_A4_arbitrary_heavier_append_cores']+=1
        ct['independent_BOTH_relatives']+=2
    # True generalized-subword ideal enumeration; independent of the core formula.
    for case in range(144):
        a,U=profile(case%3,True);b,V=profile(case//3%3,True)
        if case%2:
            t=max(max(U+[2]),b+sum(V)-a-sum(U),rng.randint(4,22));U=U+[t]
            assert a+sum(U)>=b+sum(V)
        M=max([1]+U+V)+rng.randint(1,7)
        H,L,R=core(boxes(a,U),boxes(b,V),M)
        host=[1]*a+U+[M]+list(reversed([1]*b+V))
        actual=greedy_ideal(host);assert actual==H and UI(actual)
        ct['independent_GREEDY_distinct_composition_ORIGINAL_ideals']+=1
        ct['independent_GREEDY_ORIGINAL_rank_counts']+=len(actual)
        sha.update(str((host,actual,L,R)).encode())
    qa=json.loads((ROOT/'audit_binary_ternary_A2_original_family.json').read_text())
    assert qa['status']=='EXACT_QA_PASS_BINARY_TERNARY_FULL_A2_AND_ORIGINAL_FAMILY_UNDER_PROOF_AUDIT'
    local=['binary_ternary_A2_original_family_proof.tex','BinaryTernaryA2SourceCone.lean','BinaryTernaryA2SourceCone.log',
      'audit_binary_ternary_A2_original_family.py','audit_binary_ternary_A2_original_family.json','verify_binary_ternary_A2_original_family.py']
    deps=['all_binary_ternary_complete_C_verification.json','all_binary_ternary_complete_C_proof.tex',
      'two_nonbinary_complete_C_verification.json','two_nonbinary_complete_C_proof.tex',
      'clipped_forward_ratio_frontier.tex','ClippedForwardRatio.lean','ClippedForwardRatio.log',
      'C_to_coupled_S_rising_window.tex','CToCoupledSRisingWindow.lean','CToCoupledSRisingWindow.log',
      'source_birth_gap_nonrecovery.tex','ordinary_relative_growth.tex','agent_bothdeclining_first_birth.tex',
      'agent_half_lc_actual_weak_curvature.tex','actual_half_tail_curvature_verification.json',
      'signed_kernel_extension.tex','SignedWindowTail.lean','SignedWindowTail.log',
      'deficit_cumulative_ratios.tex','inductive_signed_window.tex','short_prefix_reflection_join.tex',
      'general_base_join_route.tex','formal_arm_extensions.tex','prefix_tp2.tex','verify_subdegree_CI_entrance.py']
    out=dict(status='PASS_BINARY_TERNARY_AND_KAPPA_FOUR_CERTIFIED_CLASS_FULL_A2_AND_ORIGINAL_COEFFICIENT_FAMILY',
      new_scoped_reports=10,kernels=kernel(),
      class_definition='A4=B3(ALL1alpha2u3r) ORbinary-plus-ONE-arbitrary-tail1alpha2uT ORat-most-TWO-arbitrary-nonone-parts. ALLpadding/counts/capacitiesUNBOUNDED. Rectangles/emptyincluded. ALLCproved,nonrectkappa<=4,FINALdeletionclosed.',
      full_A2='PROVEDFULL2^n*(Delta(qXqY))^+UIforEVERYpairX,YinA4. FullOLD_A2induction,NOTshortprefixIH. HeavieronepartandALLrectangularbasesexplicit;ANYlegalappendwindowbelowNEWfirstmode<a,includingequalweights.',
      source_cone='PROVEDBOTHnonrectA4:ENTIRErawE=(2-z)qXqYpositivepartUIwithINITIALpositiveinterval,negative-terminalcoefficientKEPT. A1fromCindependentofA2. Qpost-LASTmodefromC BOTHrising+NEWtinykappa<=4mixed+OLDallranksBOTHnoninc. FULLoldA2head+entireplateau+Q+A1splicedWITHOUTzero/signhole.',
      new_mixed='PROVEDANYactualnonrectowner/oppositekappa3..4/sourceprefixNONDECR:tailNONRECOVERY,INCLUDINGowner/oppositecountsONE. Skeletoncurvature+lowercenterreflection;ONLYexceptionkappa4/alpha1/H2r2paidby(r1)C<=d. NOFINITEentrance/NOhead/A2/C/signguard.',
      original_family='PROVEDORIGINALUNAMPLIFIEDcoefficientUIforCOREandBOTHrelativepolynomials,EVERYA4pair,ALLstrictcentralpeaksM>maxarmpart. FullA2+proper-relativeprefix+deletion/exchange/least-peakbasejoin. Includesunboundedcentralpeak/unboundedbinaryandternarycounts/botharbitrarybinary-tailcapacities.',
      heavier_append='PROVEDFULLA2andORIGINALCORE/BOTHrelativesforX=Zt,YwithZ,YinA4,ANYlegalfinalt,wtX>=wtY. NewsourceexcludedbelowNEWfirstmode;noC/kappaassertionfornewXrequired. Originalfamilydeletionclosed. Lowerpeakiflargest>tremoveoppositemaxima,preserveheaviness;iflargest=tremovequalifyingjumpfirstthenstripA4maxima.',
      general_principle='SAMEproofANYfinal-deletion-closedactualarmclasswithFULLCandeveryNONRECTkappa<=4=>FULLpairA2+ORIGINALcore/BOTHrelativesALLstrictpeaks,plusONEarbitraryheavierappend.',
      formal_scope='TENNEWcleanstandard-axiomSCOPEDgenericreports. Wholefunctionpositive-sourceUIsplice/NOholes,exactdyadicraw-sourceidentity/signtransfer,small-kappareflection/birth/curvature/halfguard/modearithmetic. OLDwhole-signed-windowkernelREUSED. Actualarmmembership/sourceidentitiesandinductive/least-counterexampleassemblyWRITTEN;NOTendtoendLeancompositions. Nofinitepremiseused;ALLnumericsdiagnosticsONLY.',
      general_original='OPEN',general_C='OPEN',general_A2='OPEN',all_binary_ternary_original_coefficients='PROVED',
      counts=dict(ct),primary_QA=qa['counts'],independent_state_sha256=sha.hexdigest(),seconds=time.monotonic()-st,
      local_files=local,dependency_files=deps,sha256={n:hashlib.sha256(((ROOT if n in local else SOURCE)/n).read_bytes()).hexdigest() for n in local+deps})
    (ROOT/'binary_ternary_A2_original_family_verification.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if k not in ['sha256','kernels']}),flush=True)
if __name__=='__main__':main()
