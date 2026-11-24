"""Independent degree/maximum-part grammar and positive-suffix-box reconstruction.

The finite classifications are exact Python, not an end-to-end Lean word model.
All positive-curvature source sums are independently matched to the public
kernel certificate, including their individual coefficient operands.
"""
from pathlib import Path
from fractions import Fraction
from math import comb
from functools import lru_cache
from collections import Counter
import sys,json,time,hashlib,gzip,re
import os
ROOT=Path(os.environ.get('ONE_DESCENT_REPLAY_DIR', Path(__file__).resolve().parent))
SOURCE=Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from audit_joint_structure import fastconv
def at(p,n):return p[n] if 0<=n<len(p) else 0
def canonical(x):return (json.dumps(x,separators=(',',':'))+'\n').encode()
def parts_max(n,h,cap):
    if h==1:
        if 1<=n<=cap:yield (n,)
        return
    for largest in range((n+h-1)//h,min(cap,n-h+1)+1):
        for rest in parts_max(n-largest,h-1,largest):yield rest+(largest,)
def product_ratio(r,e,m):
    if m<0 or m>r:return Fraction(0)
    result=Fraction(1)
    for v in range(m):result*=Fraction(r-v,r+e+3+v)
    return result
@lru_cache(None)
def binary_boxes(alpha,u):
    # Sum of all suffix boxes, with binomial coefficients for each binary box.
    out=[0]*(alpha+2*u+1)
    for j in range(u):
        for k in range(j+1):out[j+k]+=comb(j,k)
    for k in range(u+1):
        value=comb(u,k)
        for l in range(alpha+1):out[u+k+l]+=value
    return tuple(out)
@lru_cache(50000)
def nonbinary_suffix_boxes(V):
    P=[1];B=[]
    for t in reversed(V):
        if len(B)<len(P):B += [0]*(len(P)-len(B))
        for i,x in enumerate(P):B[i]+=x
        P=fastconv(P,[0]+[1]*t)
    return tuple(P),tuple(B)
@lru_cache(16000)
def positive_boxes(alpha,U):
    u=0
    while u<len(U) and U[u]==2:u+=1
    seed=binary_boxes(alpha,u)
    if u==len(U):return seed
    P,B=nonbinary_suffix_boxes(U[u:]);A=fastconv(P,seed)
    for i,x in enumerate(B):A[i]+=x
    return tuple(A)
def reports(name,count):
    src=(ROOT/(name+'.lean')).read_text(encoding='utf8')
    log=(ROOT/(name+'.log')).read_text(encoding='utf8')
    assert not any(x in src for x in ['native_decide','sorry','axiom '])
    assert not any(x in log for x in ['warning:','error:','sorryAx','ofReduceBool','failed'])
    rows=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",log,re.S)
    assert len(rows)==count,(name,len(rows))
    result={n:[x.strip() for x in v.split(',') if x.strip()] for n,v in rows}
    assert all(set(a)<={'propext','Classical.choice','Quot.sound'} for a in result.values())
    return result
def main():
    start=time.monotonic();data=json.loads((ROOT/'first_missing_twelve_head_certificate_data.json').read_text(encoding='utf8'))
    ranks={};rational=set();head=set();payments=set();ct=Counter();layer_i=0
    # Independent order: K, initial padding, TOTAL degree, reverse rank.
    for K in range(10,13):
      S=(1+(K-2)*(K-1)//2)//2
      for alpha in range(1,K-5):
        d=K-alpha
        for D in range(2,min(2*d*(d-3),12*d-25)+1):
          hmax=min(D,3 if d<=6 else 5 if d<=8 else D)
          for r in range((D-2)//2+1):
            e=D-2*r-2
            if e>d-3:continue
            jmax=alpha+D+hmax-r
            row=dict(K=K,alpha=alpha,d=d,e=e,r=r,D=D,hmax=hmax,S=S,jmax=jmax)
            if jmax-2<=S:row['kind']='rank_head';head.add((jmax-2,S))
            else:
                L=d-e-3
                p=product_ratio(r,e,L)+sum(2**(i-2)*product_ratio(r,e,L+i) for i in range(2,K-2))-Fraction(e+1,r+1)
                row.update(numerator=p.numerator,denominator=p.denominator)
                row['kind']='rank_source' if p>=0 else 'owner_complement'
                if p>=0:rational.update([p.numerator,p.denominator-1])
            ranks[(K,alpha,D,r)]=row
    assert len(ranks)==len(data['ALL_rank_states'])==3241
    assert len({(x['K'],x['alpha'],x['D'],x['r']) for x in data['ALL_rank_states']})==3241
    allsha=hashlib.sha256();criticalsha=hashlib.sha256();byK=[]
    criticalpath=ROOT/'first_missing_twelve_critical_rows.jsonl.gz'
    with gzip.open(criticalpath,'rb') as critical:
      for K in range(10,13):
        kc=Counter();seen=set()
        # Order below only canonicalizes hashes after independent rank coverage.
        for inputrow in (x for x in data['ALL_rank_states'] if x['K']==K):
          row=ranks[(K,inputrow['alpha'],inputrow['D'],inputrow['r'])]
          assert row==inputrow
          alpha,D,r,e,d,S=(row[x] for x in ['alpha','D','r','e','d','S'])
          kc['complete_rank_states']+=1
          if row['kind']=='rank_head':kc['rank_strict_head_paid']+=1;continue
          if row['kind']=='rank_source':kc['rank_source_paid']+=1;continue
          kc['unpaid_rank_states']+=1
          hmin=max(2,S+3-alpha-D+r);hmax=min(D,3 if d<=6 else 5 if d<=8 else D)
          lc=Counter();lsha=hashlib.sha256()
          for h in range(hmin,hmax+1):
            for ds in sorted(parts_max(D,h,D)):
              if ds[0]>alpha:continue
              U=tuple(x+1 for x in ds);seen.add((alpha,U));A=positive_boxes(alpha,U);a=alpha+D+h
              assert len(A)==a+1
              sr=at(A,a-r)-at(A,a-r+1)
              C=at(A,a-r-1)-2*at(A,a-r)+at(A,a-r+1)
              lc['all']+=1;kc['complete_owner_rank_inputs']+=1
              state=[K,alpha,list(U),r,sr,C,'noncritical']
              if sr<0 or C<=0:
                lc['noncritical']+=1;kc['noncritical_owner_edges']+=1
              else:
                j=a-r;n=j+1-K
                terms=[at(A,n)]+[at(A,n-i) for i in range(2,K-2)]
                pay=terms[0]+sum((1<<i)*x for i,x in enumerate(terms[1:]))
                assert C<=pay,(K,alpha,U,r,C,pay)
                state=[K,alpha,list(U),r,sr,C,'source_paid',j,n,terms,pay]
                encoded=canonical(state);assert critical.readline()==encoded
                criticalsha.update(encoded);payments.add((C,tuple(terms)))
                lc['critical']+=1;kc['positive_curvature_owner_edges']+=1;kc['direct_owner_source_paid']+=1
              encoded=canonical(state);allsha.update(encoded);lsha.update(encoded)
          layer=dict(K=K,alpha=alpha,D=D,r=r,e=e,hmin=hmin,hmax=hmax,counts=dict(lc),all_state_sha256=lsha.hexdigest())
          assert layer==data['ALL_complement_layers'][layer_i],(layer,layer_i)
          layer_i+=1
        kc['distinct_canonical_owners']=len(seen);ct.update(kc)
        item=dict(K=K,S=(1+(K-2)*(K-1)//2)//2,counts=dict(kc));byK.append(item)
        print(json.dumps(dict(K=K,counts=dict(kc),seconds=time.monotonic()-start)),flush=True)
      assert critical.read()==b''
    assert layer_i==len(data['ALL_complement_layers'])==399
    assert dict(ct)==data['counts'] and byK==data['by_K']
    assert allsha.hexdigest()==data['ALL_owner_state_sha256']
    assert criticalsha.hexdigest()==data['critical_stream_sha256']
    assert hashlib.sha256(criticalpath.read_bytes()).hexdigest()==data['critical_compressed_sha256']
    assert sorted(rational)==data['rational_integer_margins']
    assert [list(x) for x in sorted(head)]==data['head_rank_pairs']
    assert [[C,list(T)] for C,T in sorted(payments)]==data['critical_source_payments']
    obligations=[f'decide ((0 : Int) ≤ {v})' for v in sorted(rational)]
    obligations += [f'decide (({j} : Int) ≤ {S})' for j,S in sorted(head)]
    for C,terms in sorted(payments):
        expr=str(terms[0])+'+'+'+'.join(str(2**i)+'*'+str(x) for i,x in enumerate(terms[1:]))
        obligations.append(f'decide (({C} : Int) ≤ {expr})')
    assert len(obligations)==data['kernel_obligations']==75372
    modules=[];wholeinputs=[];wholetheorems=[];modulefiles=[];chunkcount=0
    for base in range(0,len(obligations),2500):
        index=base//2500;module='FirstMissingTwelveCriticalPart'+str(index).zfill(2)
        modules.append(module);modulefiles += [module+'.lean',module+'.log']
        src=(ROOT/(module+'.lean')).read_text(encoding='utf8');log=(ROOT/(module+'.log')).read_text(encoding='utf8')
        assert not any(x in src for x in ['native_decide','sorry','axiom '])
        assert not any(x in log for x in ['warning:','error:','sorryAx','failed'])
        chunks=[];inputs=[]
        for i in range(base,min(base+2500,len(obligations)),100):
            name='chunk_'+str(i//100);inputname='inputs_'+str(i//100)
            chunks.append(name);inputs.append(inputname);expr=' && '.join(obligations[i:i+100]);chunkcount+=1
            assert 'private def '+inputname+' : Bool := '+expr in src
            assert 'private theorem '+name+' : '+inputname+' = true := by decide' in src
        wi='allInputsPart_'+str(index);wt='allPaymentsPart_'+str(index)
        wholeinputs.append(wi);wholetheorems.append(wt)
        public='def '+wi+' : Bool := '+' && '.join(inputs)+'\ntheorem '+wt+' : '+wi+' = true := by\n  simp only ['+', '.join([wi]+chunks+['Bool.and_self'])+']'
        assert public in src
    src=(ROOT/'FirstMissingTwelveCriticalCertificate.lean').read_text(encoding='utf8')
    assert all('import '+x in src for x in modules)
    public='theorem complete_all_rank_and_critical_source_payments : ('+' && '.join(wholeinputs)+') = true := by\n  simp only ['+', '.join(wholetheorems+['Bool.and_self'])+']'
    assert public in src and chunkcount==754 and len(modules)==31
    result=dict(status='PASS_INDEPENDENT_COMPLETE_FIRST_MISSING_TEN_THROUGH_TWELVE_SOURCE_OR_HEAD_CERTIFICATE',
      counts=dict(ct),by_K=byK,kernel_obligations=len(obligations),chunks=chunkcount,modules=len(modules),
      ALL_owner_state_sha256=allsha.hexdigest(),critical_stream_sha256=criticalsha.hexdigest(),
      independent_model='Positive binary binomial suffix boxes plus cached nonbinary suffix boxes. Degree/reverse-rank and maximum-part grammars; product-fraction source ratios. ALL noncritical and critical owner states reconstructed; EVERY critical operand and public kernel obligation matched.',
      formal_scope='All critical source SUM inequalities, all rational numerator/denominator signs and strict-head rank pairs checked in Lean. Finite word grammar and noncritical classifications independently exact, NOT end-to-end Lean.',
      kernels={'FirstMissingTwelveHeadGuards':reports('FirstMissingTwelveHeadGuards',4),
               'FirstMissingTwelveCriticalCertificate':reports('FirstMissingTwelveCriticalCertificate',1)},
      general_original='OPEN',general_C='OPEN',general_A2='OPEN',seconds=time.monotonic()-start)
    files=['build_first_missing_twelve_head_certificate.py','first_missing_twelve_head_certificate_data.json',
      'first_missing_twelve_critical_rows.jsonl.gz','FirstMissingTwelveCriticalCertificate.lean',
      'FirstMissingTwelveCriticalCertificate.log','FirstMissingTwelveHeadGuards.lean','FirstMissingTwelveHeadGuards.log',
      'verify_first_missing_twelve_head_certificate.py','build_first_missing_twelve_lean.ps1']+modulefiles
    result['sha256']={n:hashlib.sha256((ROOT/n).read_bytes()).hexdigest() for n in files}
    (ROOT/'first_missing_twelve_head_certificate_verification.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in result.items() if k not in ['sha256','kernels']}),flush=True)
if __name__=='__main__':main()
