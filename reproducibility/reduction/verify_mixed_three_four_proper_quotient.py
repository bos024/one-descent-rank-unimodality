"""Independent closed multinomial CI counts, q-basis and reversed forward division."""
from pathlib import Path
from math import comb
from collections import Counter
import sys,json,time,hashlib,re
ROOT=Path(__file__).resolve().parent
SOURCE=Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from audit_renewal_root_primitive_cut import RootField
def ci(r,s):
    P3=[sum(comb(r,k)*comb(r-k,n-2*k) for k in range(max(0,n-r),(n//2)+1) if 0<=n-2*k<=r-k) for n in range(2*r+1)]
    P4=[sum(comb(s,k)*comb(s,n-2*k) for k in range(s+1) if 0<=n-2*k<=s) for n in range(3*s+1)]
    E=[0]*(2*r+3*s+1)
    for i,x in enumerate(P3):
        for j,y in enumerate(P4):E[i+j]+=x*y
    return E
def fpow(f,a,n):
    v=f.one
    for _ in range(n):v=f.mul(v,a)
    return v
def proper_forward(f,E):
    q=f.q;l=f.add(f.one,f.add(q,f.mul(q,q)));a=f.sub(l,f.one);al=f.mul(l,a)
    H=[]
    for n,en in enumerate(E):
        v=f.scale(f.one,en)
        if n:v=f.sub(v,f.mul(al,H[-1]))
        if n>=2:v=f.sub(v,f.mul(l,H[-2]))
        H.append(v)
    return [f.mul(l,v) for v in reversed(H[:-2])]
def reports():
    src=(ROOT/'MixedThreeFourProperQuotient.lean').read_text();log=(ROOT/'MixedThreeFourProperQuotient.log').read_text()
    assert not any(s in log for s in ['warning:','error:','sorryAx','ofReduceBool','failed']) and 'native_decide' not in src
    rows=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",log,re.S);assert len(rows)==9
    out={}
    for n,raw in rows:
        ax=[s.strip() for s in raw.split(',') if s.strip()];assert set(ax)<={'propext','Classical.choice','Quot.sound'};out[n]=ax
    return out
def main():
    st=time.monotonic();ct=Counter();sha=hashlib.sha256();f=RootField(3);b=f.q
    l=f.add(f.one,f.add(b,f.mul(b,b)));a=f.sub(l,f.one)
    keys={(r,s) for r in [32,33,40,55,80,120] for s in [0,1,2,5,10,15,20,30,40]}
    keys|={(3*s-4+d,s) for s in range(16,77,3) for d in [0,9]}
    for r,s in sorted(keys):
        norm=f.scale(fpow(f,b,r+1),4**s)
        if f.sign(f.sub(f.one,f.scale(norm,64)))<0:continue
        E=ci(r,s);J=proper_forward(f,E)
        R0=f.sub(f.one,J[0]);R1=f.sub(f.sub(f.scale(f.one,r+s),J[1]),f.mul(a,J[0]))
        for n,en in enumerate(E):
            v=f.zero
            if n<len(J):v=f.add(v,J[n])
            if 0<=n-1<len(J):v=f.add(v,f.mul(a,J[n-1]))
            if 0<=n-2<len(J):v=f.add(v,f.mul(b,J[n-2]))
            if n==0:v=f.add(v,R0)
            if n==1:v=f.add(v,R1)
            assert v==f.scale(f.one,en);ct['independent_COMPLETEproper_division_identity_reads']+=1
        observed=f.add(f.sub(f.mul(b,f.mul(R0,R0)),f.mul(a,f.mul(R0,R1))),f.mul(R1,R1));assert observed==norm
        for v in [R0,R1]:assert f.sign(f.sub(f.one,f.scale(v,4)))>=0 and f.sign(f.add(f.one,f.scale(v,4)))>=0
        for v in J:assert f.sign(v)>0;ct['independent_entire_J_positive_coefficients']+=1
        for n in range(1,len(J)-1):
            assert f.sign(f.sub(f.mul(J[n],J[n]),f.mul(J[n-1],J[n+1])))>=0
            ct['independent_entire_J_GLOBAL_LC_minors']+=1
        if s and s%2==0:
            Eold=ci(r,s-1);old=proper_forward(f,Eold)
            oldR0=f.sub(f.one,old[0]);oldR1=f.sub(f.sub(f.scale(f.one,r+s-1),old[1]),f.mul(a,old[0]))
            assert R0==f.scale(oldR0,2) and R1==f.scale(oldR1,2)
            predicted=[f.zero]*len(J)
            for i,v in enumerate(old):
                for j in range(4):predicted[i+j]=f.add(predicted[i+j],v)
            predicted[0]=f.sub(predicted[0],oldR0)
            predicted[1]=f.add(f.sub(predicted[1],oldR1),f.mul(l,oldR0))
            predicted[2]=f.add(predicted[2],f.mul(l,oldR1))
            assert predicted==J;ct['independent_full_forward_THREErank_correction_hosts']+=1
        ct['independent_norm_cone_hosts']+=1
        sha.update(str((r,s,R0,R1,J[:5],J[-3:])).encode())
    primary=json.loads((ROOT/'audit_mixed_three_four_proper_quotient.json').read_text())
    assert primary['status']=='EXACT_QA_PASS_MIXED_THREE_FOUR_PROPER_QUOTIENT_NORM_CONE'
    local=['mixed_three_four_proper_quotient_proof.tex','MixedThreeFourProperQuotient.lean','MixedThreeFourProperQuotient.log',
      'audit_mixed_three_four_proper_quotient.py','audit_mixed_three_four_proper_quotient.json','verify_mixed_three_four_proper_quotient.py']
    deps=['tribonacci_rich_reverse_quotient_verification.json','tribonacci_rich_reverse_quotient_proof.tex',
      'TribonacciRichReverseQuotient.lean','TribonacciRichReverseQuotient.log','TribonacciRichReverseCertificate.lean','TribonacciRichReverseCertificate.log',
      'infinite_three_four_reference_C_verification.json','InfiniteThreeFourReference.lean','InfiniteThreeFourReference.log',
      'probe_tribonacci_quadratic_inverse.py','build_tribonacci_rich_reverse_certificate.py','audit_renewal_root_primitive_cut.py']
    out=dict(status='PASS_UNBOUNDED_THREE_FOUR_PROPER_QUADRATIC_QUOTIENT_NORM_CONE_BY_FORWARD_HEAD_REPAIR',new_scoped_reports=9,kernels=reports(),
      theorem='ALLr>=32/s>=0,b^(r+1)*4^s<=1/64:ACTUALproperdivision[3]^r[4]^s=(1+a*z+b*z2)J+R0+R1z hasSTRICTLYpositive/GLOBALLYordinaryLC J, BOTHremaindersinquarterbox. ExplicitALLs>=16/r>=3s-4. NOTzero-truncatedFPS.',
      forward_locality='WHOLE[4]=2-P3 yieldsJnew=[4]J-(1-lambda*z)(R0+R1z),Rnew=2R. CorrectionONLYranks0/1/2;centres>=4areEXACTunmodifiedLCconvolutionminors. ALLmissingcentres1,2,3andpositiveJ0,J1,J2explicitlypaid.',
      robust_head='NEWfield-independentheadforALLREALw>=32,a/bin[0,1],R0/R1quarterbox. ExactE2/E3/E4bounds=>J0[3/4,5/4],J1[L1,w1/4],J2[L2,E2],J3[L3,U3],J4<=U4. THREEwholeunivariatepositivepolynomialsatw32+X payALLTHREEheadminors;fullrecursionboundassemblykernelchecked.',
      whole_cone='EXACTremainderN=bR0²-aR0R1+R1²=b^(r+1)4^s. Priorcoercivity=>quarterbox. Fixr>=32,REUSEOLDpure3ALLr>=18globalJLC,addFOURfactorsbyincreasingnormTARGETinduction:EVERYearliernorm<=TARGET. NOunboundeddiagonalfiniteentrance.',
      explicit_cone='ALLs>=16/r+4>=3s:Nb³<=4^s*b^(3s)=(4b³)^s<=(2/3)^s,b³>=1/8=>N<=8(2/3)^16<1/64,r>=44>32. CompleteALLNatpowers/indexarithmetickernelchecked.',
      formal_scope='NINEnewcleanstandardaxiomSCOPEDreports:ALLrealheadpolynomials/genericintervalminor/proper4correction/normscale/whole2countnorm/wholeincreasingTARGETinduction/unitmixture/FULLTHREEheadminorpayment/ALLexplicitcone. OLDpure3quotientcoercivity/rootcertificatesREUSEDNOTrecounted. Properdivision/LCconvolution/wholemodelassemblyWRITTEN,notactualcompositionformalization. NOnewfiniteproofpremise.',
      general_original='OPEN',general_C='OPEN',general_A2='OPEN',mixed_three_four_single_arm_C='OPEN',positive_primitive_J_LC='NOT_ASSERTED',
      next='NEWJordinaryLC canfeedCUMULATIVEJwhosepositiveprimitiveAFTER0isJ,andALLORDERt3signedcutwithMANDATORY[2]futureinverse. RetainB3remainderdegree1/startups/finiteones/OTHERactualsourcecomponents. ActualordinarytailCbridgeSTILLNEEDSproof.',
      counts=dict(ct),primary_QA=primary['counts'],independent_state_sha256=sha.hexdigest(),seconds=time.monotonic()-st,
      local_files=local,dependency_files=deps,sha256={n:hashlib.sha256(((ROOT if n in local else SOURCE)/n).read_bytes()).hexdigest() for n in local+deps})
    (ROOT/'mixed_three_four_proper_quotient_verification.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k not in ['sha256','kernels']}),flush=True)
if __name__=='__main__':main()
