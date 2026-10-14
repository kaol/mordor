// Mordor — E3 three-crossing census engine, Round 21 (v3.2).
//
// Census result (this round): all 49 canonical three-crossing routing classes on E3
// refuted — 89,881,554 commuting pairs censused, 4,008,643 exact refutations,
// sat = 0, cap = 0, dfk = 0, u0 = 0, mx = 0, mism = 0 in every class; every kill is
// pure propagation (prp = surv). With the block-diagonal, one-crossing and
// two-crossing rounds (R17–R20) this closes E3: the Three-Crossing Theorem, and
// Theorem C — CL holds on E3, the third proven class after finite chains and E2.
// Full data: data/e3-three-crossing-census.json. Round write-up: docs/rounds/21-v3.2.md.
//
// Reproduction: set SPEC below per class, e.g. "100.120:-4:0:35:0:35:110000" (mode -4 =
// recount then solve; survivors must equal recN). Classes with recN > ~105,000 should be
// run in a0-slices, "cls:-4:0:15:0:35:110000" then "cls:-4:15:35:0:35:110000"; the slice
// sums must equal the mode -3 full recount. 100.221 runs in mode -1 (T1-probe + auto-added
// {0,2}-interfaces at j = 0, 1). The default SPEC below runs the three validation anchors.
//
// Modes: >=0 anchor (assert survivors === mode) | -1 production | -2 base-stack solve only
// | -3 recount only (recN + perA0) | -4 recount then solve (effB = min(budget, recN+2000)).
// SPEC entries "cls:mode:lo0:hi0:lo1:hi1:budget", comma-separated; defaults 0:35:0:35:110000.

// Mordor — E3 three-crossing census engine v4 (Round 21). Rebuilt from the validated
// R19/R20 two-crossing engine (experiments/e3-two-crossing-census.ts) with:
//  - general scheduled commutation: condition k (comp[A[RB[k]]][B[k]] === comp[B[RA[k]]][A[k]],
//    with H4 relief when RA[RB[k]] !== RB[RA[k]]) checked at b-level max(k, RA[k]);
//  - general lazy interface tables (i0,i1,j), 40-cell sub-CSPs, key (A[i0],A[i1],B[j]),
//    computed only for needed keys (T1 prefilter);
//  - SPEC-driven modes: >=0 anchor (assert survivors===mode), -1 production
//    (T1-probe 40 pairs, auto-add <=2 marginal interface tables, recount, solve),
//    -3 recount only (recN + perA0), -4 recount then solve (effB=min(budget,recN+2000)).
// SPEC entries: "cls:mode:lo0:hi0:lo1:hi1:budget", comma-separated; defaults 0:35:0:35:110000.
// Anchors (must reproduce exactly): 001.010 -> 3814 | 012.021 -> 9271 | 021.021 -> 23751
// recount anchors: 000.100 -> 147672 | 001.101 -> 147672 (perA0 0:5325,4:32625,14:44397,34:65325)
// Every census must report: sat=0, cap=0, dfk=0, u0=0, mx=0, mism=0, surv===recN.

const SPEC = "001.010:3814:0:35:0:35:110000,012.021:9271:0:35:0:35:110000,021.021:23751:0:35:0:35:110000";

async function main() {
const le=new Uint16Array(11),dn=new Uint16Array(11);
const CV=[[0,1],[1,2],[2,3],[3,10],[0,4],[4,5],[5,6],[6,10],[0,7],[7,8],[8,9],[9,10]];
for(let i=0;i<11;i++){le[i]=1<<i;dn[i]=1<<i;}
for(const c of CV){le[c[0]]|=1<<c[1];dn[c[1]]|=1<<c[0];}
let ch=1;while(ch){ch=0;for(let i=0;i<11;i++)for(let j=0;j<11;j++){
if((le[i]&(1<<j))&&(le[i]|le[j])!==le[i]){le[i]|=le[j];ch=1;}
if((dn[j]&(1<<i))&&(dn[j]|dn[i])!==dn[j]){dn[j]|=dn[i];ch=1;}}}
const T=[],tk=new Map();
for(let a=0;a<5;a++)for(let b=a;b<5;b++)for(let c=b;c<5;c++){tk.set(a*100+b*10+c,T.length);T.push([a,b,c]);}
const ap=(m,p)=>p===0?0:p===4?4:T[m][p-1];
const comp=[];for(let u=0;u<35;u++){comp[u]=new Uint8Array(35);for(let v=0;v<35;v++){let k=0;for(let p=1;p<4;p++)k=k*10+ap(u,ap(v,p));comp[u][v]=tk.get(k);}}
const h4b=new Uint8Array(35);for(const i of [0,4,14,34])h4b[i]=1;
const e3=(i,p)=>p===0?0:p===4?10:3*i+p;
const bm=(r,M)=>{const m=new Uint8Array(11);m[10]=10;for(let k=0;k<3;k++)for(let p=1;p<4;p++)m[3*k+p]=e3(r[k],ap(M[k],p));return m;};
const LG=new Uint8Array(2048);for(let i=0;i<11;i++)LG[1<<i]=i;
const PC=new Uint8Array(2048);for(let i=1;i<2048;i++)PC[i]=PC[i>>1]+(i&1);
const Q=new Int16Array(400),IQ=new Uint8Array(264);
function ac3g(d,AR,INC){const nn=AR.length;IQ.fill(0,0,nn);let qs=0,qe=0;
for(let i=0;i<nn;i++){Q[qe++]=i;IQ[i]=1;}
while(qs!==qe){const ai=Q[qs++];if(qs===400)qs=0;IQ[ai]=0;
const c1=AR[ai][0],c2=AR[ai][1];
let t=0,m=d[c2];while(m){t|=dn[LG[m&-m]];m&=m-1;}
const n1=d[c1]&t;let t2=0,m2=n1;while(m2){t2|=le[LG[m2&-m2]];m2&=m2-1;}
const n2=d[c2]&t2;
if(n1!==d[c1]||n2!==d[c2]){if(!n1||!n2)return 0;d[c1]=n1;d[c2]=n2;
for(const c of INC[c1])if(!IQ[c]){Q[qe++]=c;IQ[c]=1;if(qe===400)qe=0;}
for(const c of INC[c2])if(!IQ[c]){Q[qe++]=c;IQ[c]=1;if(qe===400)qe=0;}}}
return 1;}
const AR=[];for(const c of CV)for(let w=0;w<11;w++){AR.push([c[0]*11+w,c[1]*11+w]);AR.push([w*11+c[0],w*11+c[1]]);}
const INC=Array.from({length:121},()=>[]);AR.forEach((a,i)=>{INC[a[0]].push(i);INC[a[1]].push(i);});
function un(a,b){const d=new Uint16Array(121);
for(let x=0;x<11;x++){const ax=a[x],da=dn[ax],dx=dn[x];
for(let y=0;y<11;y++){const by=b[y];let s=2047;
if(y===ax)s=1<<ax;if(x===by)s=(y===ax&&ax!==by)?0:1<<by;
if(!((da>>y)&1))s&=~le[y];if(!((dx>>by)&1))s&=~dn[x];
if(!s)return null;d[x*11+y]=s;}}return d;}
let WIT=null;
function solve(a,b,mxref){const d=un(a,b);if(!d)return 0;if(!ac3g(d,AR,INC))return 1;
let NN=0,res=3;
const go=(dd)=>{NN++;if(NN>300){res=4;return 1;}
let bc=-1,bp=99;for(let c=0;c<121;c++)if(dd[c]>1&&PC[dd[c]]<bp){bp=PC[dd[c]];bc=c;}
if(bc<0){res=2;WIT=dd.slice();return 1;}
let m=dd[bc];
while(m){const v=1<<LG[m&-m];m&=m-1;const nd=dd.slice();nd[bc]=v;
if(ac3g(nd,AR,INC)){let sg=1;for(let c=0;c<121;c++)if(nd[c]&(nd[c]-1)){sg=0;break;}
if(sg){res=2;WIT=nd.slice();return 1;}if(go(nd))return 1;}}
return 0;};
const fin=go(d);if(NN>mxref.v)mxref.v=NN;return fin?res:3;}

function runEntry(e){
const RA=e.cls.slice(0,3).split("").map(Number),RB=e.cls.slice(4,7).split("").map(Number);
const out={cls:e.cls,mode:e.mode,lo0:e.lo0,hi0:e.hi0,lo1:e.lo1,hi1:e.hi1};
const t1=new Uint8Array(11025);
{const ax=new Uint8Array(5),by=new Uint8Array(5);
for(let i=0;i<3;i++)for(let j=0;j<3;j++){const B0=(i*3+j)*1225;
for(let u=0;u<35;u++){for(let p=0;p<5;p++)ax[p]=e3(RA[i],ap(u,p));
for(let v=0;v<35;v++){for(let q=0;q<5;q++)by[q]=e3(RB[j],ap(v,q));
let ok=1;
for(let p=0;p<5&&ok;p++){const x=e3(i,p),dx=dn[x];
for(let q=0;q<5&&ok;q++){const y=e3(j,q);let s=2047;
if(y===ax[p])s=1<<ax[p];if(x===by[q])s=(y===ax[p]&&ax[p]!==by[q])?0:1<<by[q];
if(!((dn[ax[p]]>>y)&1))s&=~le[y];if(!((dx>>by[q])&1))s&=~dn[x];
if(!s)ok=0;}}
t1[B0+u*35+v]=ok;}}}}
let nk=0;
function mkIF(i0,i1,j){
const val=new Uint8Array(42875),kn=new Uint8Array(42875);
const S=[0,e3(i0,1),e3(i0,2),e3(i0,3),10,e3(i1,1),e3(i1,2),e3(i1,3)];
const XC=[[0,1],[1,2],[2,3],[3,4],[0,5],[5,6],[6,7],[7,4]];
const ARI=[];for(const c of XC)for(let q=0;q<5;q++)ARI.push([c[0]*5+q,c[1]*5+q]);
for(let q=0;q<4;q++)for(let x=0;x<8;x++)ARI.push([x*5+q,x*5+q+1]);
const INI=Array.from({length:40},()=>[]);ARI.forEach((a,i)=>{INI[a[0]].push(i);INI[a[1]].push(i);});
const d=new Uint16Array(40),ax=new Uint8Array(8);
function get(u,w,v){const kb=u*1225+w*35+v;
if(kn[kb])return val[kb];
ax[0]=0;ax[4]=10;
for(let p=1;p<4;p++)ax[p]=e3(RA[i0],ap(u,p));
for(let p=1;p<4;p++)ax[p+4]=e3(RA[i1],ap(w,p));
let ok=1;
for(let q=0;q<5&&ok;q++){const y=e3(j,q),by=e3(RB[j],ap(v,q));
for(let xi=0;xi<8&&ok;xi++){const x=S[xi],A1=ax[xi];let s=2047;
if(y===A1)s=1<<A1;if(x===by)s=(y===A1&&A1!==by)?0:1<<by;
if(!((dn[A1]>>y)&1))s&=~le[y];if(!((dn[x]>>by)&1))s&=~dn[x];
if(!s)ok=0;else d[xi*5+q]=s;}}
if(ok)ok=ac3g(d,ARI,INI)?1:0;
kn[kb]=1;val[kb]=ok;nk++;return ok;}
return {get,i0,i1,j};}
const tabs=[[],[],[]];
tabs[0].push(mkIF(0,1,0));tabs[1].push(mkIF(0,1,1));tabs[2].push(mkIF(0,1,2));
const rk=[(RA[RB[0]]===RB[RA[0]])?1:0,(RA[RB[1]]===RB[RA[1]])?1:0,(RA[RB[2]]===RB[RA[2]])?1:0];
const L0=[],L1=[],L2=[];
for(let k=0;k<3;k++){const L=Math.max(k,RA[k]);if(L===0)L0.push(k);else if(L===1)L1.push(k);else L2.push(k);}
const M0=new Uint8Array(35),M1=new Uint8Array(35),M2=new Uint8Array(35);
function enumP(useIF,stride,maxStore){
let n=0,m=0,trunc=0;const perA0=new Uint32Array(35);
let list=new Uint8Array(6*4096);let capc=4096;
outer:
for(let a0=e.lo0;a0<e.hi0;a0++){
for(let a1=e.lo1;a1<e.hi1;a1++){
for(let a2=0;a2<35;a2++){
const A3=[a0,a1,a2];
for(let v=0;v<35;v++){
let mm=t1[a0*35+v]&t1[3675+a1*35+v]&t1[7350+a2*35+v];
if(mm&&useIF){const tb=tabs[0];for(let ti=0;ti<tb.length;ti++){const t=tb[ti];mm&=t.get(A3[t.i0],A3[t.i1],v);if(!mm)break;}}
M0[v]=mm;
mm=t1[1225+a0*35+v]&t1[4900+a1*35+v]&t1[8575+a2*35+v];
if(mm&&useIF){const tb=tabs[1];for(let ti=0;ti<tb.length;ti++){const t=tb[ti];mm&=t.get(A3[t.i0],A3[t.i1],v);if(!mm)break;}}
M1[v]=mm;
mm=t1[2450+a0*35+v]&t1[6125+a1*35+v]&t1[9800+a2*35+v];
if(mm&&useIF){const tb=tabs[2];for(let ti=0;ti<tb.length;ti++){const t=tb[ti];mm&=t.get(A3[t.i0],A3[t.i1],v);if(!mm)break;}}
M2[v]=mm;}
const aab0=RB[0]===0?a0:RB[0]===1?a1:a2,aab1=RB[1]===0?a0:RB[1]===1?a1:a2,aab2=RB[2]===0?a0:RB[2]===1?a1:a2;
for(let b0=0;b0<35;b0++){if(!M0[b0])continue;
let ok=1;
for(let li=0;li<L0.length;li++){const cab=comp[aab0][b0];
if(cab!==comp[b0][a0]||(!rk[0]&&!h4b[cab])){ok=0;break;}}
if(!ok)continue;
for(let b1=0;b1<35;b1++){if(!M1[b1])continue;
ok=1;
for(let li=0;li<L1.length;li++){const k=L1[li];
const cab=comp[k===0?aab0:aab1][k===0?b0:b1];
if(cab!==comp[RA[k]===0?b0:b1][k===0?a0:a1]||(!rk[k]&&!h4b[cab])){ok=0;break;}}
if(!ok)continue;
for(let b2=0;b2<35;b2++){if(!M2[b2])continue;
ok=1;
for(let li=0;li<L2.length;li++){const k=L2[li];
const cab=comp[k===0?aab0:k===1?aab1:aab2][k===0?b0:k===1?b1:b2];
if(cab!==comp[RA[k]===0?b0:RA[k]===1?b1:b2][k===0?a0:k===1?a1:a2]||(!rk[k]&&!h4b[cab])){ok=0;break;}}
if(!ok)continue;
n++;perA0[a0]++;
if(n%stride===0){
if(m===capc){if(m>=3000000){trunc=1;break outer;}capc*=2;const nl=new Uint8Array(6*capc);nl.set(list);list=nl;}
const o=m*6;list[o]=a0;list[o+1]=a1;list[o+2]=a2;list[o+3]=b0;list[o+4]=b1;list[o+5]=b2;m++;
if(maxStore&&m>=maxStore)break outer;}}}}}}}
return {n,m,list,trunc,perA0};}
function solvePass(list,m,effB){
const mx={v:0};let sat=0,cap=0,dfk=0,prp=0,u0=0,mism=0,done=0,partial=0,wit=null;
for(let i=0;i<m;i++){const o=i*6;
const a0=list[o],a1=list[o+1],a2=list[o+2],b0=list[o+3],b1=list[o+4],b2=list[o+5];
if(i<200){const a=bm(RA,[a0,a1,a2]),b=bm(RB,[b0,b1,b2]);
let c=1;for(let x=0;x<11;x++)if(a[b[x]]!==b[a[x]]){c=0;break;}
if(!c)mism++;}
if(effB&&done>=effB){partial=1;break;}
const r=solve(bm(RA,[a0,a1,a2]),bm(RB,[b0,b1,b2]),mx);
if(r===0)u0++;else if(r===1)prp++;
else if(r===2){sat++;
const F=[];for(let x=0;x<11;x++){const row=[];for(let y=0;y<11;y++)row.push(LG[WIT[x*11+y]]);F.push(row);}
const a=bm(RA,[a0,a1,a2]),b=bm(RB,[b0,b1,b2]);let ver=1;
for(const c of CV)for(let w=0;w<11;w++){if(F[c[0]][w]>F[c[1]][w])ver=0;if(F[w][c[0]]>F[w][c[1]])ver=0;}
for(let x=0;x<11;x++){if(F[x][a[x]]!==a[x])ver=0;if(F[b[x]][x]!==b[x])ver=0;}
for(let x=0;x<11;x++){let y=10;while(F[x][y]!==y)y=F[x][y];if(y!==a[x])ver=0;}
for(let y=0;y<11;y++){let x=0;while(F[x][y]!==x)x=F[x][y];if(x!==b[y])ver=0;}
wit={F,ver};break;}
else if(r===4)cap++;else dfk++;
done++;}
return {sat,cap,dfk,prp,u0,mx:mx.v,mism,done,partial,wit};}
if(e.mode===-1){
let pr=enumP(false,1000,40);
if(pr.m<40)pr=enumP(false,1,40);
const cands=[[0,2,0],[0,2,1],[0,2,2],[1,2,0],[1,2,1],[1,2,2]].map(c=>mkIF(c[0],c[1],c[2]));
let baseAlive=0;const candAlive=[0,0,0,0,0,0];
for(let i=0;i<pr.m;i++){const o=i*6;
const A=[pr.list[o],pr.list[o+1],pr.list[o+2]],B=[pr.list[o+3],pr.list[o+4],pr.list[o+5]];
let alive=1;
for(let j=0;j<3;j++){const tb=tabs[j][0];if(!tb.get(A[tb.i0],A[tb.i1],B[j])){alive=0;break;}}
if(alive){baseAlive++;
for(let ci=0;ci<6;ci++){const tb=cands[ci];if(tb.get(A[tb.i0],A[tb.i1],B[tb.j]))candAlive[ci]++;}}}
const ord=[0,1,2,3,4,5].sort((x,y)=>candAlive[x]-candAlive[y]);
const adds=[];
for(const ci of ord){if(adds.length>=2)break;
if(candAlive[ci]<baseAlive){const tb=cands[ci];tabs[tb.j].push(tb);adds.push({t:""+tb.i0+tb.i1+"@"+tb.j,alive:candAlive[ci]});}}
out.probe={m:pr.m,baseAlive,adds};}
const rc=enumP(true,1,0);
out.recN=rc.n;out.trunc=rc.trunc;out.nk=nk;
const pa={};for(let i=0;i<35;i++)if(rc.perA0[i])pa[i]=rc.perA0[i];
out.perA0=pa;
if(e.mode===-3)return out;
let effB=0;
if(e.mode===-4||e.mode===-1)effB=Math.min(e.budget,rc.n+2000);
else if(e.mode===-2)effB=e.budget;
const sp=solvePass(rc.list,rc.m,effB);
out.surv=rc.n;out.done=sp.done;out.sat=sp.sat;out.cap=sp.cap;out.dfk=sp.dfk;out.prp=sp.prp;out.u0=sp.u0;out.mx=sp.mx;out.mism=sp.mism;out.effB=effB;out.partial=sp.partial;
if(sp.wit)out.wit=sp.wit;
if(e.mode>=0)out.ok=(rc.n===e.mode)?1:0;
return out;}

const entries=SPEC.split(",").map(s=>{const f=s.split(":");return{cls:f[0],mode:+f[1],
lo0:f.length>2?+f[2]:0,hi0:f.length>3?+f[3]:35,lo1:f.length>4?+f[4]:0,hi1:f.length>5?+f[5]:35,
budget:f.length>6?+f[6]:110000};});
const res=[];
for(const en of entries)res.push(runEntry(en));
return res;
}
