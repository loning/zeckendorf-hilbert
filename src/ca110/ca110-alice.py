# ca_rule110_system.py
# ============================================================
# Zero-exogenous reversible CA system (most-atomic):
#  - 1D ring lattice
#  - Physical core = Micro-core = RULE-110 (2nd-order reversible)
#  - Propose -> Commit (Lexicographic potential + free flip + minimal history)
#  - Boundary pair toggling (split/merge) + block mapping interfaces
#  - Ports (upstream / lateral) affect permission & lexicographic prefix (no writes to child-CA)
#  - Local holographic inverse
#  - Chi-phase (2 or 3) scheduler
# ============================================================

from __future__ import annotations
from dataclasses import dataclass, field
from typing import Callable, Dict, List, Sequence, Tuple, Optional
import math
import random

# -----------------------------
# Bit helpers (Boolean gates)
# -----------------------------
def bxor(a: int, b: int) -> int: return (a ^ b) & 1
def band(a: int, b: int) -> int: return (a & b) & 1
def bor(a: int, b: int) -> int:  return (a | b) & 1
def bnot(a: int) -> int:         return a ^ 1
def beq(a: int, b: int) -> int:  return (a ^ b) ^ 1
def parity(bits: Sequence[int]) -> int:
    s = 0
    for v in bits: s ^= (v & 1)
    return s & 1

# ---------------------------------------------------
# RULE-110 LUT (8-bit truth table, index 4L+2C+R)
# ---------------------------------------------------
RULE110: Tuple[int, ...] = tuple([
    0,  # 000
    1,  # 001
    1,  # 010
    1,  # 011
    0,  # 100
    1,  # 101
    1,  # 110
    0,  # 111
])
def f_rule110(Lb: int, Cb: int, Rb: int) -> int:
    return RULE110[(Lb<<2)|(Cb<<1)|Rb] & 1

# ============================================================
# Law Track L (all rules/constants live here; runtime L is fixed)
# ============================================================
@dataclass
class LawTrack:
    # cores
    ell_110: Tuple[int, ...] = RULE110
    # sigma: summary from micro-CA (y)
    sigma: Callable[[Sequence[int]], int] = staticmethod(lambda y: parity(y))
    # theta: local phase from x-neighborhood + sigma
    theta: Callable[[int, int, int, int], int] = staticmethod(lambda xL,xC,xR,s: parity([xL,xC,xR,s]))
    # raw tendency
    G_L: Callable[[Tuple[int,...], int, int], int] = staticmethod(lambda phi,g,theta: bxor(parity(phi), bxor(g,theta)))
    # Guard (Trap-free)
    Guard_allowed: Callable[[int,int,int,int,int], Tuple[int,int]] = None  # to be set below
    # Lexicographic potential vector H(e)
    LexOrder_H: Callable[..., Tuple[int,...]] = None  # to be set below
    # Free autonomy (optional pre-commit reversible rearrangements)
    U_free: Callable[[Tuple[int,...], Tuple[int,...]], Tuple[Tuple[int,...], Tuple[int,...]]] \
        = staticmethod(lambda m_bits, h_bits: (m_bits, h_bits))
    # free flip function
    Phi_free: Callable[[Tuple[int,...], int, int], int] = staticmethod(lambda m_bits, s, theta: bxor(parity(m_bits), bxor(s, theta)))
    # Block mapping pack/unpack (interfaces)
    B_mu_pack: Callable[[Tuple[Tuple[int,...], ...]], Tuple[int, ...]] = staticmethod(lambda block: tuple(sum((list(b) for b in block), [])))
    B_mu_unpack: Callable[[Tuple[int, ...], int], Tuple[Tuple[int,...], ...]] = staticmethod(lambda macro,mu: tuple(tuple(macro[j:j+mu]) for j in range(0,len(macro),mu)))
    # commit phases
    chi: int = 2
    # a->x coupling
    h_L_mode: str = "zero"  # "zero" or "id"
    # consensus mode
    hard_consensus: bool = False  # if True, Guard will narrow permission when M_up=1

    def __post_init__(self):
        # Default Guard: allowed0 ≡ 1; allowed1 = B ∧ (pL ∨ pC ∨ pR ∨ theta)
        def guard_allowed(pL: int, pC: int, pR: int, B: int, theta: int) -> Tuple[int,int]:
            allowed0 = 1
            allowed1 = band(B, bor(bor(pL, pC), bor(pR, theta)))
            return allowed0, allowed1
        self.Guard_allowed = guard_allowed

        # Default H vector: (H_up, H_lat, H_11, H_00, H_dens, H_budget, H_split)
        def lex_H(e: int, *, pL:int,pC:int,pR:int, aL:int,aC:int,aR:int,
                  B:int, M_up:int, D_up:int, M_lat:int, D_lat:int, bL:int,bR:int) -> Tuple[int,...]:
            H_up  = band(M_up, (e ^ D_up))
            H_lat = band(M_lat, (e ^ D_lat))
            H11   = band(self.Guard_allowed(pL,pC,pR,B,0)[1], band(e, bor(pL,pR)))
            H00   = band(1, band(bnot(e), bor(bnot(pL), bnot(pR))))
            all1  = (aL & e & aR) & 1
            all0  = (bnot(aL) & bnot(e) & bnot(aR)) & 1
            Hden  = (all1 | all0) & 1
            Hbud  = band(bnot(B), e)   # e=1 costs when budget is 0
            Hspl  = bxor(1 if (bL==bR) else 0, e)  # toy: mismatch with boundary parity
            return (H_up, H_lat, H11, H00, Hden, Hbud, Hspl)
        self.LexOrder_H = lex_H

# ============================================================
# Cell & Universe
# ============================================================
@dataclass
class Cell:
    # physical two frames
    x_prev: int; x_cur: int
    # consensus state
    a: int; p: int
    # memory/ports (gene g read-only; B budget; ports: M_up,D_up,M_lat,D_lat)
    m: Dict[str,int] = field(default_factory=lambda: {"g":0,"B":1,"M_up":0,"D_up":0,"M_lat":0,"D_lat":0})
    # minimal history: (eta=e*, k, rho=pHat, u, dB) -- all bits
    h: Tuple[int, ...] = field(default_factory=tuple)
    # micro-CA two frames
    y_prev: Tuple[int, ...] = field(default_factory=tuple)
    y_cur:  Tuple[int, ...] = field(default_factory=tuple)
    # summary + phase
    s: int = 0; theta: int = 0
    # boundary bit
    b: int = 0

@dataclass
class Universe:
    N: int
    mu: int
    L: LawTrack
    cells: List[Cell]

    # -------------- ring helpers --------------
    def left(self,i:int)->int:  return (i-1) % self.N
    def right(self,i:int)->int: return (i+1) % self.N

    # -------------- recompute s, theta --------------
    def recompute_sigma_theta(self)->None:
        for i in range(self.N):
            self.cells[i].s = self.L.sigma(self.cells[i].y_cur)
        for i in range(self.N):
            Lc = self.cells[self.left(i)].x_cur
            Cc = self.cells[i].x_cur
            Rc = self.cells[self.right(i)].x_cur
            self.cells[i].theta = self.L.theta(Lc,Cc,Rc,self.cells[i].s)

    # -------------- features & pHat --------------
    def features_phi(self,i:int)->Tuple[int,...]:
        Lc = self.cells[self.left(i)]
        Cc = self.cells[i]
        Rc = self.cells[self.right(i)]
        # purely local & Boolean features; no real numbers
        return (Lc.x_cur, Cc.x_cur, Rc.x_cur, Cc.s, Cc.m["B"], bxor(Cc.x_prev,Cc.x_cur))
    def p_hat(self,i:int)->int:
        Cc = self.cells[i]
        phi = self.features_phi(i)
        return self.L.G_L(phi, Cc.m["g"], Cc.theta) & 1

    # -------------- propose (reversible XOR write) --------------
    def propose(self)->List[int]:
        pHat = [self.p_hat(i) for i in range(self.N)]
        for i in range(self.N):
            self.cells[i].p = bxor(self.cells[i].p, pHat[i])
        return pHat

    # -------------- commit one phase --------------
    def commit_phase(self, pHat: List[int], phase: int)->None:
        # local snapshot of a for density penalty
        a_snap = [c.a for c in self.cells]
        # autonomy gate (optional): leave identity by default
        for i in range(self.N):
            if (i % self.L.chi) != phase: continue
            c = self.cells[i]
            # example U_free works on tuple memory; here we maintain tuple from dict for formality
            m_bits = tuple([c.m["g"], c.m["B"], c.m["M_up"], c.m["D_up"], c.m["M_lat"], c.m["D_lat"]])
            _, _ = self.L.U_free(m_bits, c.h)  # identity

        # compute & write
        for i in range(self.N):
            if (i % self.L.chi) != phase: continue
            c   = self.cells[i]
            iL, iR = self.left(i), self.right(i)
            allowed0, allowed1 = self.L.Guard_allowed(pHat[iL], pHat[i], pHat[iR], c.m["B"], c.theta)

            # H vectors
            H0 = self.L.LexOrder_H(0,
                    pL=pHat[iL],pC=pHat[i],pR=pHat[iR],
                    aL=a_snap[iL],aC=a_snap[i],aR=a_snap[iR],
                    B=c.m["B"], M_up=c.m["M_up"], D_up=c.m["D_up"],
                    M_lat=c.m["M_lat"], D_lat=c.m["D_lat"],
                    bL=self.cells[iL].b, bR=self.cells[iR].b)
            H1 = self.L.LexOrder_H(1,
                    pL=pHat[iL],pC=pHat[i],pR=pHat[iR],
                    aL=a_snap[iL],aC=a_snap[i],aR=a_snap[iR],
                    B=c.m["B"], M_up=c.m["M_up"], D_up=c.m["D_up"],
                    M_lat=c.m["M_lat"], D_lat=c.m["D_lat"],
                    bL=self.cells[iL].b, bR=self.cells[iR].b)

            # if hard_consensus: narrow permission to force directive
            if self.L.hard_consensus and c.m["M_up"]==1:
                if c.m["D_up"]==1:
                    allowed0 = 0; allowed1 = 1
                else:
                    allowed0 = 1; allowed1 = 0

            # default e by lexicographic order
            if H0 < H1: e_def = 0
            elif H1 < H0: e_def = 1
            else: e_def = c.theta & 1

            # free flip only when both allowed
            both = band(allowed0, allowed1)
            k = band(self.L.Phi_free(tuple([c.m["g"], c.m["B"], c.m["M_up"], c.m["D_up"], c.m["M_lat"], c.m["D_lat"]]),
                                     c.s, c.theta), both)
            e_star = bxor(e_def, k)

            # boundary toggle (pair) using u = pHat[i] as toy reversible driver
            u = pHat[i]

            # reversible writes: a, B, boundary pair, history
            self.cells[i].a = bxor(self.cells[i].a, e_star)
            B_next = bnot(e_star)  # policy
            dB = bxor(B_next, c.m["B"])
            self.cells[i].m["B"] = B_next

            j = self.right(i)
            self.cells[i].b   = bxor(self.cells[i].b, u)
            self.cells[j].b   = bxor(self.cells[j].b, u)

            # history minimal set
            self.cells[i].h = (e_star & 1, k & 1, pHat[i] & 1, u & 1, dB & 1)

    # -------------- physical/micro step (2nd-order reversible) --------------
    def phys_micro(self)->None:
        # physical
        xnext = [0]*self.N
        for i in range(self.N):
            Lb = self.cells[self.left(i)].x_cur
            Cb = self.cells[i].x_cur
            Rb = self.cells[self.right(i)].x_cur
            fx = f_rule110(Lb,Cb,Rb)
            coup = self.cells[i].a if self.L.h_L_mode=="id" else 0
            xnext[i] = bxor(self.cells[i].x_prev, bxor(fx, coup))
        # micro-CA
        ynext: List[Tuple[int,...]] = []
        for i in range(self.N):
            mu = len(self.cells[i].y_cur)
            nxt = [0]*mu
            for j in range(mu):
                Lb = self.cells[i].y_cur[(j-1)%mu]
                Cb = self.cells[i].y_cur[j]
                Rb = self.cells[i].y_cur[(j+1)%mu]
                fx = f_rule110(Lb,Cb,Rb)
                nxt[j] = bxor(self.cells[i].y_prev[j], fx)
            ynext.append(tuple(nxt))
        # roll
        for i in range(self.N):
            self.cells[i].x_prev, self.cells[i].x_cur = self.cells[i].x_cur, xnext[i]
            self.cells[i].y_prev, self.cells[i].y_cur = self.cells[i].y_cur, ynext[i]

    # -------------- one full step --------------
    def step(self, t_phase: int)->None:
        self.recompute_sigma_theta()
        pHat = self.propose()
        # commit phases
        for ph in range(self.L.chi):
            self.commit_phase(pHat, phase=( (t_phase + ph) % self.L.chi ))
        # phys/micro
        self.phys_micro()
        # ready next theta/sigma
        self.recompute_sigma_theta()

    # -------------- inverse step (local holography) --------------
    def step_inverse(self, t_phase: int)->None:
        # If a->x coupled, need a^t for x rollback.
        # Strategy:
        #   if h_L="id": inverse commit first (to restore a^t), then inverse phys/micro;
        #   else ("zero"): inverse phys/micro first, then inverse commit.
        def inv_phys_micro():
            # invert x,y (second-order)
            x_prev_old = [0]*self.N
            for i in range(self.N):
                Lb = self.cells[self.left(i)].x_prev
                Cb = self.cells[i].x_prev
                Rb = self.cells[self.right(i)].x_prev
                fx = f_rule110(Lb,Cb,Rb)
                coup = self.cells[i].a if self.L.h_L_mode=="id" else 0
                x_prev_old[i] = bxor(self.cells[i].x_cur, bxor(fx, coup))
            y_prev_old: List[Tuple[int,...]] = []
            for i in range(self.N):
                mu = len(self.cells[i].y_prev)
                prev = [0]*mu
                for j in range(mu):
                    Lb = self.cells[i].y_prev[(j-1)%mu]
                    Cb = self.cells[i].y_prev[j]
                    Rb = self.cells[i].y_prev[(j+1)%mu]
                    fx = f_rule110(Lb,Cb,Rb)
                    prev[j] = bxor(self.cells[i].y_cur[j], fx)
                y_prev_old.append(tuple(prev))
            # roll back frames
            for i in range(self.N):
                self.cells[i].x_cur  = self.cells[i].x_prev
                self.cells[i].x_prev = x_prev_old[i]
                self.cells[i].y_cur  = self.cells[i].y_prev
                self.cells[i].y_prev = y_prev_old[i]

        def inv_commit_phase(phase:int):
            # inverse boundary, budget, a, clear history
            # We do NOT recompute anything; use stored (eta,k,rho,u,dB)
            for i in range(self.N):
                if (i % self.L.chi) != phase: continue
                h = self.cells[i].h
                if not h: continue
                eta, k, rho, u, dB = (h + (0,0,0,0,0))[:5]
                # undo boundary pair toggle
                j = self.right(i)
                self.cells[i].b = bxor(self.cells[i].b, u)
                self.cells[j].b = bxor(self.cells[j].b, u)
                # undo budget & action
                self.cells[i].m["B"] = bxor(self.cells[i].m["B"], dB)
                self.cells[i].a      = bxor(self.cells[i].a, eta)
                # clear history
                self.cells[i].h = tuple()

        def inv_propose():
            # recompute or use rho; we recompute to depend only on local state
            self.recompute_sigma_theta()
            pHat = [self.p_hat(i) for i in range(self.N)]
            for i in range(self.N):
                # if history had rho, we could use it; recompute is fine (state restored to t)
                self.cells[i].p = bxor(self.cells[i].p, pHat[i])

        if self.L.h_L_mode == "id":
            # inverse commit in reverse phase order
            for rph in reversed(range(self.L.chi)):
                inv_commit_phase( (t_phase + rph) % self.L.chi )
            inv_phys_micro()
            inv_propose()
        else:
            # zero-coupling: invert phys/micro first
            inv_phys_micro()
            for rph in reversed(range(self.L.chi)):
                inv_commit_phase( (t_phase + rph) % self.L.chi )
            inv_propose()
        # recompute for next round
        self.recompute_sigma_theta()

    # -------------- metrics & checks --------------
    def inverse_check(self, t_phase:int)->bool:
        # copy current snapshot
        snap = [Cell(**vars(c)) for c in self.cells]
        self.step(t_phase)
        self.step_inverse(t_phase)
        ok = True
        for a,b in zip(snap, self.cells):
            if not (a.x_prev==b.x_prev and a.x_cur==b.x_cur and a.a==b.a and a.p==b.p and
                    a.m==b.m and a.y_prev==b.y_prev and a.y_cur==b.y_cur and a.b==b.b):
                ok = False; break
        return ok

    def freedom_ratio(self)->float:
        # fraction of sites with allowed1==1 (allowed0 ≡ 1)
        self.recompute_sigma_theta()
        pHat = [self.p_hat(i) for i in range(self.N)]
        cnt = 0
        for i in range(self.N):
            a0,a1 = self.L.Guard_allowed(pHat[self.left(i)], pHat[i], pHat[self.right(i)],
                                         self.cells[i].m["B"], self.cells[i].theta)
            if a1==1: cnt += 1
        return cnt/float(self.N)

    def a_equal3_ratio(self)->float:
        a=[c.a & 1 for c in self.cells]; eq=0
        for i in range(self.N):
            if a[self.left(i)]==a[i]==a[self.right(i)]: eq+=1
        return eq/float(self.N)

# ============================================================
# Builders & Demo
# ============================================================
def make_lawtrack_default(*, chi:int=2, h_L_mode:str="zero", hard_consensus:bool=False)->LawTrack:
    L = LawTrack(chi=chi, h_L_mode=h_L_mode, hard_consensus=hard_consensus)
    return L

def make_universe(N:int=64, mu:int=5, L:Optional[LawTrack]=None)->Universe:
    if L is None:
        chi = 2 if (N%2==0) else 3
        L = make_lawtrack_default(chi=chi, h_L_mode="zero", hard_consensus=False)
    cells: List[Cell] = []
    for i in range(N):
        x_prev = (i>>0)&1
        x_cur  = (i>>1)&1
        a      = (i>>2)&1
        p      = (i>>3)&1
        # memory/ports: seed by index (pure bits, no constants out of L)
        m = {"g":(i>>4)&1, "B":(i>>5)&1, "M_up":0, "D_up":1, "M_lat":0, "D_lat":0}
        y_prev = tuple(((i+j)&1) for j in range(mu))
        y_cur  = tuple((((i+1)+j)&1) for j in range(mu))
        s=0; theta=0; b=(i & 1); h=tuple()
        cells.append(Cell(x_prev,x_cur,a,p,m,h,y_prev,y_cur,s,theta,b))
    U = Universe(N=N, mu=mu, L=L, cells=cells)
    U.recompute_sigma_theta()
    return U

# ============================================================
# Example main
# ============================================================
if __name__ == "__main__":
    N = 64
    mu = 5
    L  = make_lawtrack_default(chi=(2 if N%2==0 else 3), h_L_mode="zero", hard_consensus=False)
    U  = make_universe(N=N, mu=mu, L=L)

    # 1) Inverse check (information conservation & local holography)
    ok = U.inverse_check(t_phase=0)
    print("[Inverse Check]", "OK" if ok else "FAIL")

    # 2) Advance several steps and report metrics
    T = 24
    for t in range(1, T+1):
        U.step(t_phase=(t-1))
        if t%6==0:
            print(f"[t={t:02d}] freedom={U.freedom_ratio():.3f}  a_equal3={U.a_equal3_ratio():.3f}")

    # 3) Switch to coupled mode and re-check inverse
    L_coupled = make_lawtrack_default(chi=(2 if N%2==0 else 3), h_L_mode="id", hard_consensus=False)
    Uc = make_universe(N=N, mu=mu, L=L_coupled)
    ok2 = Uc.inverse_check(t_phase=0)
    print("[Inverse Check with a->x coupling]", "OK" if ok2 else "FAIL")

    # 4) Turn on hard consensus (upstream directive forced) and step a bit
    L_hard = make_lawtrack_default(chi=(2 if N%2==0 else 3), h_L_mode="zero", hard_consensus=True)
    Uh = make_universe(N=N, mu=mu, L=L_hard)
    for t in range(8):
        Uh.step(t_phase=t)
    print("[Hard consensus] freedom=", Uh.freedom_ratio())
