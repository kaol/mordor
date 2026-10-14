// Mordor — E₃ two-crossing class census (rounds 19–20, validated).
//
// Enumerates every commuting polar pair (a, b) on E₃ in a two-crossing routing
// class, kills unrealizable pairs with sound relaxations (T1 block unary tables,
// 40-cell interface sub-CSPs), and refutes every survivor with the exact
// realizability CSP solver (unary domains -> AC-3 on cover arcs -> MRV DFS,
// node cap 300). Exactness: chain-4 exhaustive 223 = 223 (see docs, §26.1).
//
// CONFIGURATION — one line per class census (everything else is invariant):
//   RA, RB : routing triples of a and b (source column -> target column)
//   ST     : 0 STAR (ra=[0,0,0]) | 1 CHN (ra=[0,0,1]) | 2 SGL (ra=[0,0,2])
//          | 3 ID (ra=[0,1,2])
//   LO,HI  : A[0] range for slicing large classes (full range: 0,35)
//   CLS    : class label "ra.rb"
//
// Validated anchors (must reproduce exactly):
//   001.010 -> survivors 3814  | 002.021 -> 9271  | 000.021 -> 15478
// every census: sat=0, capped=0, maxNodes=0, unary-kills=0, dfs-kills=0
// (survivors die in pure propagation).
//
// INVARIANT (tripwire): T1 over all nine blocks is equivalent to full-grid
// unary nonemptiness. A census where any survivor dies at the unary stage is
// broken between the block builder and the solver — see docs, §28.1.
//
// Runtime: ~1 minute per class in a sandboxed TypeScript runner; memory <16 MiB.

const RA=[0,0,1],RB=[0,2,1],ST=1,LO=0,HI=35,CLS="001.021";
async function main(){
// ---- E3 lattice (11 elements: bottom, three 3-chains, top) ----
const le=new Uint16Array(11),dn=new Uint16Array(11);
const CV=[[0,1],[1,2],[2,3],[3,10],[0,4],[4,5],[5,6],[6,10],[0,7],[7,8],[8,9],[9,10]];
for(let i=0;i<11;i++){le[i]=1<<i;dn[i]=1<<i;}
for(const c of CV){le[c[0]]|=1<<c[1];dn[c[1]]|=1<<c[0];}
let ch=1;while(ch){ch=0;for(let i=0;i<11;i++)for(let j=0;j<11;j++){
if((le[i]&(1<<j))&&(le[i]|le[j])!==le[i]){le[i]|=le[j];ch=1;}
if((dn[j]&(1<<i))&&(dn[j]|dn[i])!==dn[j]){dn[j]|=dn[i];ch=1;}}}
// ---- M5 column maps (35 monotone triples over positions 0..4) ----
const T=[],tk=new Map();
for(let a=0;a<5;a++)for(let b=a;b<5;b++)for(let c=b;c<5;c++){tk.set(a*100+b*10+c,T.length);T.push([a,b,c]);}
const ap=(m,p)=>p===0?0:p===4?4:T[m][p-1];
const comp=[];for(let u=0;u<35;u++){comp[u]=new Uint8Array(35);for(let v=0;v<35;v++){let k=0;for(let p=1;p<4;p++)k=k*10+ap(u,ap(v,p));comp[u][v]=tk.get(k);}}
const h4b=new Uint8Array(35);for(const i of[0,4,14,34])h4b[i]=1; // bound-only triples H4
const e3=(i,p)=>p===0?0:p===4?10:3*i+p;
const bm=(r,M)=>{const m=new Uint8Array(11);m[10]=10;for(let k=0;k<3;k++)for(let p=1;p<4;p++)m[3*k+p]=e3(r[k],ap(M[k],p));return m;};
const LG=new Uint8Array(2048);for(let i=0;i<11;i++)LG[1<<i]=i;
const PC=new Uint8Array(2048);for(let i=1;i<2048;i++)PC[i]=PC[i>>1]+(i&1);
// ---- generic AC-3 over cover arcs (full grid and interfaces) ----
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
// ---- full 11x11 grid machinery ----
const AR=[];for(const c of CV)for(let w=0;w<11;w++){AR.push([c[0]*11+w,c[1]*11+w]);AR.push([w*11+c[0],w*11+c[1]]);}
const INC=Array.from({length:121},()=>[]);AR.forEach((a,i)=>{INC[a[0]].push(i);INC[a[1]].push(i);});
// unary domains: pins, E2+ (remove ^y when y !<= a(x)), E3+ (remove v x when b(y) !<= x)
function un(a,b){const d=new Uint16Array(121);
for(let x=0;x<11;x++){const ax=a[x],da=dn[ax],dx=dn[x];
for(let y=0;y<11;y++){const by=b[y];let s=2047;
if(y===ax)s=1<<ax;if(x===by)s=(y===ax&&ax!==by)?0:1<<by;
if(!((da>>y)&1))s&=~le[y];if(!((dx>>by)&1))s&=~dn[x];
if(!s)return null;d[x*11+y]=s;}}return d;}
let MXN=0;
// returns 0 unsat-unary | 1 unsat-prop | 2 sat | 3 unsat-dfs | 4 capped
function solve(a,b){const d=un(a,b);if(!d)return 0;if(!ac3g(d,AR,INC))return 1;
let NN=0,res=3;
const go=(dd)=>{NN++;if(NN>300){res=4;return 1;}
let bc=-1,bp=99;for(let c=0;c<121;c++)if(dd[c]>1&&PC[dd[c]]<bp){bp=PC[dd[c]];bc=c;}
if(bc<0){res=2;return 1;}
let m=dd[bc];
while(m){const v=1<<LG[m&-m];m&=m-1;const nd=dd.slice();nd[bc]=v;
if(ac3g(nd,AR,INC)){let sg=1;for(let c=0;c<121;c++)if(nd[c]&(nd[c]-1)){sg=0;break;}
if(sg){res=2;return 1;}if(go(nd))return 1;}}
return 0;};
const fin=go(d);if(NN>MXN)MXN=NN;return fin?res:3;}
// ---- T1 block tables: key (i*3+j)*1225+u*35+v, 1 = no empty unary cell ----
// NOTE: cells are evaluated at their TRUE coordinates e3(i,p), e3(j,q) — the
// images a(x), b(y) enter only the constraints (§28.1 tripwire).
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
// ---- interface tables IF_j: 40-cell sub-CSP, x in col0 U col1, y in col j ----
const S=[0,1,2,3,10,4,5,6],XCV=[[0,1],[1,2],[2,3],[3,4],[0,5],[5,6],[6,7],[7,4]];
function bIF(j){const t=new Uint8Array(42875);
const ARI=[];for(const c of XCV)for(let q=0;q<5;q++)ARI.push([c[0]*5+q,c[1]*5+q]);
for(let q=0;q<4;q++)for(let x=0;x<8;x++)ARI.push([x*5+q,x*5+q+1]);
const INI=Array.from({length:40},()=>[]);ARI.forEach((a,i)=>{INI[a[0]].push(i);INI[a[1]].push(i);});
const d=new Uint16Array(40),ax=new Uint8Array(8);
for(let u=LO;u<HI;u++){for(let p=0;p<5;p++)ax[p]=e3(RA[0],ap(u,p));
for(let w=0;w<35;w++){for(let p=1;p<4;p++)ax[p+4]=e3(RA[1],ap(w,p));
const kb=u*1225+w*35;
for(let v=0;v<35;v++){let ok=1;
for(let q=0;q<5&&ok;q++){const y=e3(j,q),by=e3(RB[j],ap(v,q));
for(let xi=0;xi<8&&ok;xi++){const x=S[xi],A1=ax[xi];let s=2047;
if(y===A1)s=1<<A1;if(x===by)s=(y===A1&&A1!==by)?0:1<<by;
if(!((dn[A1]>>y)&1))s&=~le[y];if(!((dn[x]>>by)&1))s&=~dn[x];
if(!s)ok=0;else d[xi*5+q]=s;}}
if(ok&&ac3g(d,ARI,INI))t[kb+v]=1;}}}
return t;}
const IF0=bIF(0),IF1=bIF(1),IF2=bIF(2);
// ---- masked commuting enumeration + exact refutation ----
const r0=(RA[RB[0]]===RB[RA[0]])?1:0,r1=(RA[RB[1]]===RB[RA[1]])?1:0,r2=(RA[RB[2]]===RB[RA[2]])?1:0;
let surv=0,sat=0,cap=0,dfk=0,prp=0,u0=0;
const M0=new Uint8Array(35),M1=new Uint8Array(35),M2=new Uint8Array(35);
for(let a0=LO;a0<HI;a0++)for(let a1=0;a1<35;a1++)for(let a2=0;a2<35;a2++){
const ab0=RB[0]===0?a0:RB[0]===1?a1:a2,ab1=RB[1]===0?a0:RB[1]===1?a1:a2,ab2=RB[2]===0?a0:RB[2]===1?a1:a2;
const kb=a0*1225+a1*35;
for(let v=0;v<35;v++){
M0[v]=t1[a0*35+v]&t1[3675+a1*35+v]&t1[7350+a2*35+v]&IF0[kb+v];
M1[v]=t1[1225+a0*35+v]&t1[4900+a1*35+v]&t1[8575+a2*35+v]&IF1[kb+v];
M2[v]=t1[2450+a0*35+v]&t1[6125+a1*35+v]&t1[9800+a2*35+v]&IF2[kb+v];}
for(let b0=0;b0<35;b0++){if(!M0[b0])continue;const c0=comp[ab0][b0];if(c0!==comp[b0][a0]||(!r0&&!h4b[c0]))continue;
for(let b1=0;b1<35;b1++){if(!M1[b1])continue;const vm1=ST===3?b1:b0,c1=comp[ab1][b1];if(c1!==comp[vm1][a1]||(!r1&&!h4b[c1]))continue;
for(let b2=0;b2<35;b2++){if(!M2[b2])continue;const vm2=ST===0?b0:ST===1?b1:b2,c2=comp[ab2][b2];if(c2!==comp[vm2][a2]||(!r2&&!h4b[c2]))continue;
surv++;
const r=solve(bm(RA,[a0,a1,a2]),bm(RB,[b0,b1,b2]));
if(r===0)u0++;else if(r===1)prp++;else if(r===2)sat++;else if(r===4)cap++;else dfk++;
}}}}
return {CLS,LO,HI,surv,sat,cap,dfk,prp,u0,mx:MXN};}
