# most_atomic_rule110_minimal.py
# Minimal "most-atomic" RULE-110 reversible CA with lexicographic potential,
# non-interference influence via ports, exact inverse, and nested micro-CA.
# Modes: lex_mode in {"GOLD","FWO"}, free_mode in {"normal","limited"}, couple_mode in {"id","zero"}.
from collections import defaultdict
import math

# RULE-110 三邻域 LUT（索引 0..7 对应 000..111）
RULE110=[0,1,1,1,0,1,1,0]

def bxor(a,b): return (a^b)&1
def bnot(a): return a^1
def parity(bits):
    s=0
    for v in bits: s^=(v&1)
    return s&1
def rule110(L,C,R):
    return RULE110[((L&1)<<2)|((C&1)<<1)|(R&1)]&1

class Cell:
    """
    最小本地状态（仅比特）：
      x_prev,x_cur: 物理层两帧
      a,p: 共识/提案
      g: 基因位（只读；也作为“big”锚点标记）
      B: 预算位（可写）
      h: 历史位（eta,k,rho,u,dB）
      y_prev,y_cur: 子-CA 两帧（RULE110）
      s: 子-CA 摘要 σ(y_cur)
      theta: 相位
      b: 边界位（分裂/合并对拍）
    """
    __slots__=("x_prev","x_cur","a","p","g","B","h","y_prev","y_cur","s","theta","b")
    def __init__(self,x_prev,x_cur,a,p,g,B,h,y_prev,y_cur,s,theta,b):
        self.x_prev=x_prev&1; self.x_cur=x_cur&1; self.a=a&1; self.p=p&1
        self.g=g&1; self.B=B&1; self.h=tuple((bi&1) for bi in h)
        self.y_prev=tuple((bi&1) for bi in y_prev); self.y_cur=tuple((bi&1) for bi in y_cur)
        self.s=s&1; self.theta=theta&1; self.b=b&1

class Universe:
    """
    最原子可逆 CA 宇宙：
      - 物理 = 微核 = RULE-110（二阶可逆）
      - 提案/提交：势能字典序（GOLD/FWO），自由翻转（normal/limited）
      - 端口式影响（父/大只改许可/优先级，不写子内部）
      - 历史最小集 h = (eta,k,rho,u,dB)，耦合下也能精确反演
      - 物理步使用 a^t = a^{t+1} XOR eta（由历史恢复提交前的 a）
    """
    def __init__(self,N,mu=7,couple_mode="id",lex_mode="GOLD",free_mode="normal"):
        self.N=int(N); self.mu=int(mu)
        self.couple_mode=couple_mode  # "id" 或 "zero"
        self.lex_mode=lex_mode        # "GOLD" 或 "FWO"
        self.free_mode=free_mode      # "normal" 或 "limited"
    def left(self,i):  return (i-1)%self.N
    def right(self,i): return (i+1)%self.N
    # ① σ,θ 重算
    def recompute_sigma_theta(self,cells):
        for i in range(self.N):
            cells[i].s=parity(cells[i].y_cur)
        for i in range(self.N):
            Lc=cells[self.left(i)]; Cc=cells[i]; Rc=cells[self.right(i)]
            cells[i].theta=parity([Lc.x_cur,Cc.x_cur,Rc.x_cur,Cc.s])
    # φ 特征
    def features_phi(self,i,cells):
        Lc=cells[self.left(i)]; Cc=cells[i]; Rc=cells[self.right(i)]
        return (Lc.x_cur,Cc.x_cur,Rc.x_cur,Cc.s,Cc.B,(Cc.x_prev^Cc.x_cur)&1)
    # G_L: pHat
    def p_hat(self,i,cells):
        Cc=cells[i]; phi=self.features_phi(i,cells)
        s=0
        for v in phi: s^=(v&1)
        return (s ^ Cc.g ^ Cc.theta) & 1
    # Guard: allowed0≡1；allowed1 = B & (pL|pC|pR|theta)
    def allowed1(self,i,pHat,cells):
        Cc=cells[i]; L=pHat[self.left(i)]; C=pHat[i]; R=pHat[self.right(i)]
        return Cc.B & (L|C|R|Cc.theta)
    # 端口（非干预）：提供前缀指令，不写子内部
    def ports(self,i,cells):
        L=self.left(i); R=self.right(i)
        bigL=(cells[L].g==1); bigR=(cells[R].g==1)
        M_lat=1 if (bigL or bigR) else 0
        D_lat=cells[L].a if bigL else (cells[R].a if bigR else 0)
        M_up=cells[i].b; D_up=D_lat
        return M_up,D_up,M_lat,D_lat
    # 势能字典序向量（全 0/1）
    def H_vector(self,i,e,pHat,cells):
        L=self.left(i); R=self.right(i)
        M_up,D_up,M_lat,D_lat=self.ports(i,cells)
        H_up  = (M_up  & (1 if e!=D_up  else 0))&1
        H_lat = (M_lat & (1 if e!=D_lat else 0))&1
        allow1=self.allowed1(i,pHat,cells)
        H11=(allow1 & (e & (pHat[L]|pHat[R])))&1
        H00=(1 & ((e^1) & (((pHat[L]^1)|(pHat[R]^1)))))&1
        aL,aC,aR=cells[L].a,cells[i].a,cells[R].a
        Hdens=1 if ((aL==aC==e) or (aR==aC==e)) and (aL==aR) else 0
        Hbudget=1 if ((e^1)&1)==cells[i].B else 0
        Hsplit=1 if (pHat[i]!=e) else 0
        if self.lex_mode=="FWO":
            return (H_up,H_lat,H11,H00,Hdens,Hbudget,Hsplit)
        else:
            return (H11,H00,Hdens,H_up,H_lat,Hbudget,Hsplit)
    # 默认解（字典序最小；并列用 θ 破平；e=1 需合法）
    def pick_default(self,i,pHat,cells):
        allow1=self.allowed1(i,pHat,cells)
        H0=self.H_vector(i,0,pHat,cells)
        H1=self.H_vector(i,1,pHat,cells) if allow1 else (1,)*8
        if H0<H1: edef=0
        elif H1<H0: edef=1
        else: edef=cells[i].theta&1
        return edef,allow1
    # 自由翻转（仅在 both-legal）
    def free_flip(self,i,cells,allow1):
        if not allow1: return 0
        Cc=cells[i]; base=(Cc.B^Cc.g^Cc.s^Cc.theta)&1
        return (base & Cc.B) if (self.free_mode=="limited") else base
    # ③ 提交（单相）
    def commit_phase(self,cells,pHat,phase_parity):
        new=[Cell(c.x_prev,c.x_cur,c.a,c.p,c.g,c.B,c.h,c.y_prev,c.y_cur,c.s,c.theta,c.b) for c in cells]
        for i in range(self.N):
            if (i&1)!=(phase_parity&1): continue
            edef,allow1=self.pick_default(i,pHat,new)
            k=self.free_flip(i,new,allow1); e_star=(edef ^ (k & allow1)) & 1
            # a 与 B（记录 dB）
            new[i].a = new[i].a ^ e_star
            B_old=new[i].B; B_next = (e_star ^ 1) & 1; dB = B_next ^ B_old
            new[i].B = B_next
            # 边界对拍（分裂/合并）
            u=pHat[i]; j=(i+1)%self.N
            new[i].b ^= u; new[j].b ^= u
            # 历史最小集 h = (eta,k,rho,u,dB)
            new[i].h = (e_star&1, k&1, pHat[i]&1, u&1, dB&1)
        return new
    # ② 提案：p ^= pHat
    def propose(self,cells):
        pHat=[self.p_hat(i,cells) for i in range(self.N)]
        for i in range(self.N): cells[i].p ^= pHat[i]
        return pHat
    # ④ 物理/微核（二阶可逆；耦合用 a^t = a^{t+1} XOR eta）
    def phys_micro(self,cells):
        xnext=[0]*self.N
        for i in range(self.N):
            L=cells[(i-1)%self.N].x_cur; C=cells[i].x_cur; R=cells[(i+1)%self.N].x_cur
            fx=rule110(L,C,R)
            if self.couple_mode=="id":
                eta=(cells[i].h[0]&1) if len(cells[i].h)>=1 else 0
                a_t = cells[i].a ^ eta
                coup=a_t
            else: coup=0
            xnext[i] = (cells[i].x_prev ^ fx ^ coup) & 1
        ynext=[]
        for i in range(self.N):
            mu=len(cells[i].y_cur); nxt=[0]*mu
            for j in range(mu):
                L=cells[i].y_cur[(j-1)%mu]; C=cells[i].y_cur[j]; R=cells[i].y_cur[(j+1)%mu]
                fx=rule110(L,C,R); nxt[j]=(cells[i].y_prev[j]^fx)&1
            ynext.append(tuple(nxt))
        for i in range(self.N):
            cells[i].x_prev,cells[i].x_cur = cells[i].x_cur,xnext[i]
            cells[i].y_prev,cells[i].y_cur = cells[i].y_cur,ynext[i]
    # 单步
    def step(self,cells,t_phase):
        self.recompute_sigma_theta(cells)
        pHat=self.propose(cells)
        mid=self.commit_phase(cells,pHat,phase_parity=(t_phase&1))
        new=self.commit_phase(mid,pHat,phase_parity=((t_phase+1)&1))
        self.phys_micro(new); return new
    # 逆步（局部全息）
    def step_inverse(self,cells_new,t_phase):
        cells=[Cell(c.x_prev,c.x_cur,c.a,c.p,c.g,c.B,c.h,c.y_prev,c.y_cur,c.s,c.theta,c.b) for c in cells_new]
        # 逆 Commit（逆相序）
        def inv_commit(arr,phase_parity):
            new=[Cell(c.x_prev,c.x_cur,c.a,c.p,c.g,c.B,c.h,c.y_prev,c.y_cur,c.s,c.theta,c.b) for c in arr]
            for i in range(self.N):
                if (i&1)!=(phase_parity&1): continue
                if len(arr[i].h)<5: continue
                eta,k,rho,u,dB = (arr[i].h[0]&1,arr[i].h[1]&1,arr[i].h[2]&1,arr[i].h[3]&1,arr[i].h[4]&1)
                j=(i+1)%self.N
                new[i].b^=u; new[j].b^=u
                new[i].B = arr[i].B ^ dB
                new[i].a = arr[i].a ^ eta
                new[i].h = tuple()
            return new
        cells=inv_commit(cells,phase_parity=((t_phase+1)&1))
        cells=inv_commit(cells,phase_parity=(t_phase&1))
        # 逆物理/微核
        x_prev_old=[0]*self.N
        for i in range(self.N):
            L=cells[(i-1)%self.N].x_prev; C=cells[i].x_prev; R=cells[(i+1)%self.N].x_prev
            fx=rule110(L,C,R)
            coup = cells[i].a if self.couple_mode=="id" else 0
            x_prev_old[i] = (cells[i].x_cur ^ fx ^ coup) & 1
        y_prev_old=[]
        for i in range(self.N):
            mu=len(cells[i].y_prev); prv=[0]*mu
            for j in range(mu):
                L=cells[i].y_prev[(j-1)%mu]; C=cells[i].y_prev[j]; R=cells[i].y_prev[(j+1)%mu]
                fx=rule110(L,C,R); prv[j]=(cells[i].y_cur[j]^fx)&1
            y_prev_old.append(tuple(prv))
        for i in range(self.N):
            cells[i].x_cur,cells[i].x_prev = cells[i].x_prev,x_prev_old[i]
            cells[i].y_cur,cells[i].y_prev = cells[i].y_prev,y_prev_old[i]
        # 逆 Propose
        self.recompute_sigma_theta(cells)
        pHat=[self.p_hat(i,cells) for i in range(self.N)]
        for i in range(self.N): cells[i].p ^= pHat[i]
        return cells
    # 可逆核验
    def inverse_check(self,cells,t_phase):
        fwd=self.step([Cell(c.x_prev,c.x_cur,c.a,c.p,c.g,c.B,c.h,c.y_prev,c.y_cur,c.s,c.theta,c.b) for c in cells],t_phase)
        bwd=self.step_inverse(fwd,t_phase)
        for i in range(self.N):
            A=cells[i]; B=bwd[i]
            if not (A.x_prev==B.x_prev and A.x_cur==B.x_cur and A.a==B.a and A.p==B.p and A.g==B.g and A.B==B.B and A.y_prev==B.y_prev and A.y_cur==B.y_cur and A.b==B.b):
                return 0
        return 1

def init_universe(N=96,mu=7,couple_mode="id",lex_mode="GOLD",free_mode="normal"):
    """
    生成初始宇宙与状态：纯确定性种子（零外源）
    """
    U=Universe(N,mu,couple_mode,lex_mode,free_mode); cells=[]
    for i in range(N):
        x_prev=(i>>0)&1; x_cur=(i>>1)&1; a=(i>>2)&1; p=(i>>3)&1
        g=(i>>4)&1; B=(i>>5)&1
        y_prev=tuple(((i+j)&1) for j in range(mu))
        y_cur =tuple((((i+1)+j)&1) for j in range(mu))
        s=0; theta=0; b=(i&1); h=tuple()
        cells.append(Cell(x_prev,x_cur,a,p,g,B,h,y_prev,y_cur,s,theta,b))
    return U,cells
