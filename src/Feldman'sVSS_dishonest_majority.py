import secrets
import hashlib
from enum import Enum, auto
from dataclasses import dataclass
from typing import Dict, List, Tuple
from ecpy.curves import Curve
import time

# ============================================================
# Curve Setup
# ============================================================
curve = Curve.get_curve("secp256k1")
G = curve.generator
ORDER = curve.order

class MaliciousMode(Enum):
    NONE = auto()
    EVIL_DEALER_BAD_PROOF = auto()        
    EVIL_DEALER_BAD_COMMITMENT = auto()   
    BAD_REFRESH_SUB_SHARE = auto()       
    BAD_ONBOARD_SHARE = auto()           
    RECONSTRUCT_LIE = auto()             
    EVIL_DEALER_HIGH_DEGREE = auto()     
    EVIL_REFRESH_NON_ZERO = auto()


class FischlinSchnorrOfficial:
    def __init__(self, G, order, rho=16, b=8, challenge_bits=128):
        self.G = G
        self.order = order
        self.rho = rho                  # ρ: Total number of parallel repetitions
        self.b = b                      # b: Hardness parameter (target bits of zeros)
        self.challenge_bits = challenge_bits
        self.max_challenge = 1 << challenge_bits

    def encode_point(self, P):
        if P.is_infinity:
            return b"INF"
        return f"{P.x}|{P.y}".encode()

    def H_full(self, x_point, commitments, sid=b""):
        """ Step 3: common-h <- H(x, m_vec, sid) """
        data = sid + self.encode_point(x_point)
        for m_i in commitments:
            data += self.encode_point(m_i)
        return hashlib.sha256(data).digest()

    def H_b(self, common_h, i, e_i, z_i):
        """ Step 4.a.ii: h_i <- H_b(common-h, i, e_i, z_i) """
        data = (
            common_h + 
            i.to_bytes(4, "big") + 
            e_i.to_bytes((self.challenge_bits + 7) // 8, "big") + 
            z_i.to_bytes((self.order.bit_length() + 7) // 8, "big")
        )
        h = int.from_bytes(hashlib.sha256(data).digest(), "big")
        return h & ((1 << self.b) - 1)

    def prove_single(self, X, x, sid=b""):
        """ Main Prover Algorithm matching proveFischlin """
        while True:
            # 1. For i = 1,...,ρ
            m_vec = []
            sigma_vec = []
            for _ in range(self.rho):
                # (m_i, σ_i) <- ProverFirstMessage(x, w)
                r = secrets.randbelow(self.order)
                R = r * self.G
                m_vec.append(R)
                sigma_vec.append(r)  # random r generated is in  σ vector 

            # 3. common-h <- H(x, m_vec, sid)
            common_h = self.H_full(X, m_vec, sid)

            e_vec = [0] * self.rho
            z_vec = [0] * self.rho
            
            proof_failed = False

            # 4. For i = 1,...,ρ
            for i in range(self.rho):
                success_in_round = False
                
                # (a) For e_i = 0,..., 2^t - 1
                for e_i in range(self.max_challenge):
                    # i. z_i <- ProverSecondMessage(x, w, σ_i, e_i)
                    z_i = (sigma_vec[i] + e_i * x) % self.order
                    
                    # ii. h_i <- H_b(common-h, i, e_i, z_i)
                    h_i = self.H_b(common_h, i, e_i, z_i)
                    
                    # iii. If h_i == 0, break
                    if h_i == 0:
                        e_vec[i] = e_i
                        z_vec[i] = z_i
                        success_in_round = True
                        break
                
                # iv. If e_i == 2^t - 1 and no break occurred
                if not success_in_round:
                    proof_failed = True
                    break # Break out of the ρ loop to trigger an entire proof redo

            if not proof_failed:
                # 7. π <- (m_vec, e_vec, z_vec)
                return {"m": m_vec, "e": e_vec, "z": z_vec}
            
            # If proof_failed is True, the while loop continues, redoing from Step 1.

    def verify_single(self, X, proof, sid=b""):
        """ Main Verifier Algorithm matching verifyFischlin """
        m_vec = proof["m"]
        e_vec = proof["e"]
        z_vec = proof["z"]

        # 2. If m_vec, e_vec, and z_vec do not each have ρ elements, reject
        if len(m_vec) != self.rho or len(e_vec) != self.rho or len(z_vec) != self.rho:
            return False

        # 3. Range check for honest prover
        for e_i in e_vec:
            if e_i < 0 or e_i >= self.max_challenge:
                return False

        # 4. common-h <- H(x, m_vec, sid)
        common_h = self.H_full(X, m_vec, sid)

        # 5. For i in {1,...,ρ}
        for i in range(self.rho):
            m_i = m_vec[i]
            e_i = e_vec[i]
            z_i = z_vec[i]

            # (a) Halt and output reject if VerifyProof(x, m_i, e_i, z_i) == 0
            # algebraic check: z_i * G == R_i + e_i * X
            if z_i * self.G != m_i + e_i * X:
                return False

            # (b) Halt and output reject if H_b(common-h, i, e_i, z_i) != 0
            if self.H_b(common_h, i, e_i, z_i) != 0:
                return False

        # 6. Output accept
        return True


class BatchFischlinParallelValues:
    """
    Executes the specified Fischlin structure independently, 
    in parallel for each distinct public value.
    """
    def __init__(self, G, order, rho=16, b=8):
        self.engine = FischlinSchnorrOfficial(G, order, rho, b)

    def prove_batch(self, witnesses, sid=b""):
        proofs = []
        for w in witnesses:
            x_point = w * self.engine.G
            proofs.append(self.engine.prove_single(x_point, w, sid))
        return proofs

    def verify_batch(self, public_points, proofs, sid=b""):
        if len(public_points) != len(proofs):
            return False

        for x_point, pi in zip(public_points, proofs):
            if not self.engine.verify_single(x_point, pi, sid):
                return False
        return True

# ============================================================
# Batch Fiat-Shamir Proof (Hardened for Point at Infinity / Zero Scalars)
# ============================================================
class BatchFiatShamirPoK:
    def __init__(self, G, order):
        self.G = G
        self.order = order

    def _challenge(self, random_commitments, public_points, context_tag: bytes = b""):
        data = context_tag
        for R, X in zip(random_commitments, public_points):
            if R.is_infinity:
                data += b"INF"
            else:
                data += str(R.x).encode() + str(R.y).encode()
                
            if X.is_infinity:
                data += b"INF"
            else:
                data += str(X.x).encode() + str(X.y).encode()
        return int(hashlib.sha256(data).hexdigest(), 16) % self.order

    def prove_batch(self, scalars, context_tag: bytes = b""):
        random_commitments, random_scalars = [], []
        for _ in scalars:
            r = secrets.randbelow(self.order)
            random_commitments.append(r * self.G)
            random_scalars.append(r)
        public_points = [x * self.G for x in scalars]

        e = self._challenge(random_commitments, public_points, context_tag)

        responses = [(r + e * x) % self.order for r, x in zip(random_scalars, scalars)]
        return (random_commitments, responses)

    def verify_batch(self, public_points, proof, context_tag: bytes = b""):
        if not proof: return False
        random_commitments, responses = proof  
        if len(public_points) != len(random_commitments) or len(public_points) != len(responses):
            return False
        e = self._challenge(random_commitments, public_points, context_tag)
        for X, R, z in zip(public_points, random_commitments, responses):
            if z * self.G != R + e * X:
                return False
        return True

# ============================================================
# Feldman VSS Core 
# ============================================================
class FeldmanVSS:
    def __init__(self, n: int, t: int):
        self.n = n
        self.t = t
        self.G = G
        self.order = ORDER
        self.curve = curve

    def generate_polynomial(self, secret: int):
        coeffs = [secret % self.order]
        for _ in range(self.t - 1):
            coeffs.append(secrets.randbelow(self.order))
        return coeffs

    def evaluate(self, coeffs, x):
        y = 0
        for c in reversed(coeffs):
            y = (y * x + c) % self.order
        return y

    def generate_commitments(self, coeffs):
        return [c * self.G for c in coeffs]

    def verify_share(self, share, commitments, pid):
        if len(commitments) != self.t:
            return False
            
        left = share * self.G
        right = None
        for k in range(self.t):
            term = pow(pid, k, self.order) * commitments[k]
            right = term if right is None else right + term
        return left == right

    def reconstruct(self, shares):
        if len(shares) < self.t:
            raise ValueError("Need at least t shares")
        def inv(a):
            return pow(a, -1, self.order)

        secret = 0
        for i, (xi, yi) in enumerate(shares):
            li = 1
            for j, (xj, _) in enumerate(shares):
                if i != j:
                    li *= (0 - xj) * inv(xi - xj)
                    li %= self.order
            secret = (secret + yi * li) % self.order
        return secret
    
    def lagrange(self,j, indexes, target):
        num = 1
        den = 1
        for index in indexes:
            if index != j:
                num = (num * (target - index)) % ORDER
                den = (den * (j - index)) % ORDER

        return (num * pow(den, -1, ORDER)) % ORDER

# ============================================================
# Message Types 
# ============================================================
@dataclass
class ShareMessage:
    sender: int
    receiver: int
    share: int
    commitments: list
    proof: tuple

@dataclass
class RefreshCommitmentMessage:
    sender: int
    receiver: int
    commitments: list
    subshare: int


@dataclass
class ReconstructionShareMessage:
    sender: int
    receiver: int
    share: int

@dataclass
class AddShareMessage:
    sender: int
    receiver: int
    subshare: int


@dataclass
class AddPartySyncMessage:
    sender: int
    receiver: int
    commitments: list
    subshare : int

@dataclass
class CommitmentVectorSyncMessage:
    sender: int
    receiver: int
    commitment_vector: list


# ============================================================
# Performance Metrics
# ============================================================
class Metrics:
    def __init__(self):
        self.messages = {
            "TOTAL": 0,
            "INITIAL_SETUP": 0,
            "REFRESH": 0,
            "ADD": 0,
            "RECONSTRUCTION": 0
        }
        self.message_types = {}
        self.timers = {}

    def start_timer(self, name):
        self.timers[name] = time.perf_counter()

    def stop_timer(self, name):
        if name in self.timers:
            self.timers[name] = (time.perf_counter() - self.timers[name]) * 1000

    def add_time(self, name, elapsed_seconds):
        """Accumulate repeated measurements in milliseconds."""
        self.timers[name] = self.timers.get(name, 0.0) + elapsed_seconds * 1000

    def count_message(self, msg, phase):
        self.messages["TOTAL"] += 1
        self.messages[phase] += 1
        name = type(msg).__name__
        self.message_types[name] = self.message_types.get(name, 0) + 1

    def report(self):
        print("\n========== PERFORMANCE REPORT ==========")
        print("\nMessages exchanged:")
        for k, v in self.messages.items():
            print(f"{k}: {v}")

        print("\nMessage types:")
        for k, v in self.message_types.items():
            print(f"{k}: {v}")

        print("\nMeasured times:")
        for k, v in self.timers.items():
            if isinstance(v, float):
                print(f"{k}: {v:.3f} ms")
        print("========================================\n")
        self.messages = {k: 0 for k in self.messages}
        self.message_types.clear()

# ============================================================
# Network
# ============================================================
class Network:
    def __init__(self, metrics=None):
        self.queues = {}
        self.buffer = {}
        self.metrics = metrics
        self.phase = "INITIAL_SETUP"

    def register(self, pid):
        self.queues[pid] = []

    def buffer_register(self, pid):
        self.buffer[pid] = []

    def send(self, msg):
        if self.metrics:
            self.metrics.count_message(msg, self.phase)
        self.queues[msg.receiver].append(msg)

    def buffer_send(self, msg):
        if self.metrics:
            self.metrics.count_message(msg, self.phase)
        self.buffer[msg.receiver].append(msg)

    def recv_all(self, pid):
        msgs = self.queues[pid]
        self.queues[pid] = []
        return msgs
    
    def flush_buffer(self):
        for pid in self.buffer:
            self.queues[pid].extend(self.buffer[pid])
            self.buffer[pid] = []

# ============================================================
# Participant (Zero-Trust Model with Abort Hooks)
# ============================================================
class Participant:
    def __init__(self, pid, vss, network):
        self.pid = pid
        self.vss = vss
        self.network = network
        self.metrics = network.metrics
        self.share = None
        self.commitments = {}
        self.add_commitments = {}
        
        self.add_subshares = {}
        self.refresh_commitments = {}
        self.refresh_subshares = {}
        self.zk = BatchFischlinParallelValues(G, ORDER)
       # self.zk = BatchFiatShamirPoK(G, ORDER)

    def process(self):
            msgs = self.network.recv_all(self.pid)
            for msg in msgs:
                if isinstance(msg, ShareMessage):
                    if len(msg.commitments) != self.vss.t:
                        print(f"[-] P{self.pid}: [ABORT] Dealer commitment length mismatch!")
                        continue

                    start = time.perf_counter()
                    commitments_ok = self.zk.verify_batch(msg.commitments, msg.proof, b"INITIAL_SETUP")
                    if self.metrics:
                        self.metrics.add_time("ZKP_VERIFICATION", time.perf_counter() - start)
                    if not commitments_ok:
                        print(f"[-] P{self.pid}: [ABORT] Dealer zero-knowledge proof INVALID!")
                        continue

                    start = time.perf_counter()
                    share_ok = self.vss.verify_share(msg.share, msg.commitments, self.pid)
                    if self.metrics:
                        self.metrics.add_time("SHARE_VERIFICATION", time.perf_counter() - start)
                    if not share_ok:
                        print(f"[-] P{self.pid}: [ABORT] Distributed share verification FAILED!")
                        continue

                    self.share = msg.share
                    self.commitments = msg.commitments

                    for pid in range(1,self.vss.n+1):  
                        if pid == self.pid:
                            continue

                        sync_msg = CommitmentVectorSyncMessage(
                            sender=self.pid,
                            receiver=pid,
                            commitment_vector=self.commitments
                        )

                        self.network.send(sync_msg)  

                    print(f"[+] P{self.pid}: Accepted initial verified share.")

                elif isinstance(msg, CommitmentVectorSyncMessage): 
                    start = time.perf_counter()
                    commitments_match = self.commitments == msg.commitment_vector
                    if self.metrics:
                        self.metrics.add_time("COMMITMENT_VECTOR_CHECK", time.perf_counter() - start)
                    if not commitments_match:
                        print(f"[-] P{self.pid}: [ABORT] Commitment vector mismatch with P{msg.sender}!")
                    else:
                        print(f"[+] P{self.pid}: Commitment vector synchronized with P{msg.sender}.")



                elif isinstance(msg, RefreshCommitmentMessage):
                    if len(msg.commitments) != self.vss.t:
                        print(f"[-] P{self.pid}: [ABORT] Refresh commitment threshold anomaly!")
                        continue

                    self.refresh_subshares[msg.sender] = msg.subshare
                    self.refresh_commitments[msg.sender] = msg.commitments
                    if msg.commitments[0] != self.vss.curve.infinity:
                        print(f"[-] P{self.pid}: [ABORT] Refresh polynomial is not a sharing of zero!")
                        continue

                    if len(self.refresh_subshares) == self.vss.t:
                        new_commitments = []
                        for k in range(self.vss.t):
                            Bk = self.commitments[k]

                            for commits in self.refresh_commitments.values():
                                Bk += commits[k]
                            new_commitments.append(Bk)

                        new_share = self.share
                        for subshare in self.refresh_subshares.values():
                            new_share = (new_share + subshare) % ORDER
                        print(f"[+] P{self.pid}: Refresh contributions aggregated, verifying new share...")
                        


                elif isinstance(msg, AddShareMessage):
                    self.add_subshares [msg.sender] = msg.subshare
                    if len(self.add_subshares) == (self.vss.t) :
                        indexes = list(self.add_subshares.keys())
                        target_index = self.vss.n + 1
                        new_share_contribution = 0

                        for i in indexes: 
                            coeff = self.vss.lagrange(i, indexes, target_index)
                            term = (self.add_subshares[i] * coeff) % ORDER
                            new_share_contribution = (new_share_contribution + term) % ORDER
                        
                        onboard_msg = AddPartySyncMessage(
                            sender=self.pid,
                            receiver=target_index,
                            commitments=self.commitments,
                            subshare=new_share_contribution
                        )
                        self.network.buffer_send(onboard_msg)
                        

                elif isinstance(msg, AddPartySyncMessage):
                    self.add_commitments[msg.sender] = (msg.commitments , msg.subshare)
                    self.commitments = msg.commitments
                    if len(self.add_commitments) == self.vss.t: 

                        for commit,_  in self.add_commitments.values():
                            if commit != self.commitments:
                                print(f"[-] P{self.pid}: [ABORT] Commitment vector mismatch during onboarding sync!")
                                return
                        indexes = list(self.add_commitments.keys())
                        target_index = 0
                        self.share = 0 

                        for i in indexes:
                            coefficient = self.vss.lagrange(i, indexes, target_index)
                            term = (self.add_commitments[i][1] * coefficient) % ORDER
                            self.share = (self.share + term) % ORDER

                        if self.vss.verify_share(self.share, self.commitments, self.pid):
                            print(f"[+] P{self.pid}: Successfully onboarded with verified share.")
                            self.add_commitments = {}
                        else:
                            print(f"[-] P{self.pid}: [ABORT] Final share verification failed during onboarding!")


    def add(self,comitee):
            
            coeffs = [self.share]
            for _ in range(self.vss.t - 1):
                coeffs.append(secrets.randbelow(ORDER))

            self.add_subshares[self.pid] = self.vss.evaluate(coeffs, self.pid)

            for participant_id in comitee: 
                if participant_id != self.pid:
                    subshare  = self.vss.evaluate(coeffs, participant_id)
                    share_msg = AddShareMessage(
                                sender=self.pid,
                                receiver=participant_id,
                                subshare = subshare
                                )
                    self.network.buffer_send(share_msg)  

    def refresh(self,comitee):

            # 1. Generate a valid masking polynomial where f(0) = 0
        coeffs = self.vss.generate_polynomial(0)
                
        # 2. Generate raw coefficient commitments (preserving polynomial index structure)
        commits = self.vss.generate_commitments(coeffs)
        for pid in list(self.network.queues.keys()):
            if pid != self.pid:
                subshare = self.vss.evaluate(coeffs, pid)
                self.network.buffer_send(RefreshCommitmentMessage(
                    sender=self.pid, receiver=pid, commitments=commits, subshare=subshare
                        ))

            


# ============================================================
# Adversarial / Honest Dealer
# ============================================================
class Dealer:
    def __init__(self, vss, network):
        self.vss = vss
        self.network = network
        self.zk = BatchFischlinParallelValues(G, ORDER)
        #self.zk = BatchFiatShamirPoK(G, ORDER)
        self.mode = MaliciousMode.NONE

    def distribute(self, secret, participants):
        metrics = self.network.metrics

        start = time.perf_counter()
        coeffs = self.vss.generate_polynomial(secret)
        if metrics:
            metrics.add_time("POLYNOMIAL_GENERATION", time.perf_counter() - start)
        
        #  Simulate standard higher degree parameter injection attack
        if self.mode == MaliciousMode.EVIL_DEALER_HIGH_DEGREE:
            print(f"[!] Attack: Dealer generating polynomial of degree {self.vss.t} instead of {self.vss.t - 1}")
            coeffs.append(secrets.randbelow(ORDER))

        start = time.perf_counter()
        commitments = self.vss.generate_commitments(coeffs)
        if metrics:
            metrics.add_time("COMMITMENT_GENERATION", time.perf_counter() - start)

        start = time.perf_counter()
        proof = self.zk.prove_batch(coeffs, b"INITIAL_SETUP")
        if metrics:
            metrics.add_time("ZKP_GENERATION", time.perf_counter() - start)

        if self.mode == MaliciousMode.EVIL_DEALER_BAD_PROOF:
            print("[!] Attack: Dealer generating a corrupted zero-knowledge proof.")
            proof = (proof[0], [z * 2 % ORDER for z in proof[1]])

        if self.mode == MaliciousMode.EVIL_DEALER_BAD_COMMITMENT:
            print("[!] Attack: Dealer altering verification commitment structure.")
            commitments[0] = commitments[0] + G

        for p in participants.values():
            start = time.perf_counter()
            share = self.vss.evaluate(coeffs, p.pid)
            if metrics:
                metrics.add_time("SHARE_GENERATION", time.perf_counter() - start)

            start = time.perf_counter()
            self.network.send(ShareMessage(
                sender=0, receiver=p.pid, share=share, commitments=commitments, proof=proof
            ))
            if metrics:
                metrics.add_time("INITIAL_MESSAGE_DISPATCH", time.perf_counter() - start)

# ============================================================
# Protocol Management Engine
# ============================================================
class FeldmanVSSProtocol:
    def __init__(self, n, t, secret):
        self.n = n
        self.t = t
        self.vss = FeldmanVSS(n, t)
        self.metrics = Metrics()
        self.network = Network(self.metrics)
        self.participants = {}
        self.secret = secret
        #self.zk = BatchFiatShamirPoK(G, ORDER)
        self.zk = BatchFischlinParallelValues(G, ORDER)

        for pid in range(1, n + 1):
            self.network.register(pid)
            self.network.buffer_register(pid)
            self.participants[pid] = Participant(pid, self.vss, self.network)

        self.dealer = Dealer(self.vss, self.network)
        self.setup()

    def setup(self):
        self.network.phase = "INITIAL_SETUP"

        self.metrics.start_timer("INITIAL_SETUP_TOTAL")

        self.metrics.start_timer("DEALER_SETUP_AND_DISTRIBUTION")
        self.dealer.distribute(self.secret, self.participants)
        self.metrics.stop_timer("DEALER_SETUP_AND_DISTRIBUTION")

        self.metrics.start_timer("INITIAL_VERIFICATION")
        self.run_round()
        self.run_round()
        self.metrics.stop_timer("INITIAL_VERIFICATION")

        self.metrics.stop_timer("INITIAL_SETUP_TOTAL")
        self.metrics.report()

    def run_round(self):
        for p in list(self.participants.values()):
            p.process()

    def refresh(self, attacker_id=None):
            
            print("\n[REFRESH] Executing proactively timed resharding cycle...")

            #round 1
            committee = list(self.participants.keys())[:self.t]
            for provider_id in committee:
                provider = self.participants[provider_id]
                provider.refresh(committee)
            
            #round 2 
            self.network.flush_buffer()
            self.run_round()
            

    def add(self, attacker_id=None):

        self.network.phase = "ADD"

        new_pid = self.n + 1
        print(f"\n[ADD] Onboarding P{new_pid}")
        self.network.register(new_pid)
        self.network.buffer_register(new_pid)

        new_participant = Participant(new_pid, self.vss, self.network)
        self.participants[new_pid] = new_participant

        committee = list(self.participants.keys())[:self.t]

        #starting round 1 
        for provider_id in committee:
            provider = self.participants[provider_id]
            provider.add(committee)

        #starting round 2 
        self.network.flush_buffer()
        self.run_round()

        #starting round 3
        self.network.flush_buffer()
        self.run_round()


        self.n += 1
        self.vss.n +=1 



    def reconstruct(self, liar_id=None):
        print("\n[RECONSTRUCTION] Initializing verified interpolation step...")

        self.network.phase = "RECONSTRUCTION"

        combiner_id = 2
        combiner_node = self.participants[combiner_id]

        committee = list(self.participants.keys())[:self.t]

        # Add the combiner's own share exactly once.
        shares = [(combiner_id, combiner_node.share)]

        for p_id in committee:
            if p_id == combiner_id:
                continue

            participant = self.participants[p_id]
            payload_share = participant.share

            # Optional malicious reconstruction simulation.
            if liar_id == p_id:
                payload_share = (payload_share + 1) % self.vss.order

            self.network.send(
                ReconstructionShareMessage(
                    sender=p_id,
                    receiver=combiner_id,
                    share=payload_share
                )
            )

        msgs = self.network.recv_all(combiner_id)

        for msg in msgs:
            share_ok = self.vss.verify_share(
                msg.share,
                combiner_node.commitments,
                msg.sender
            )

            if not share_ok:
                print(
                    f"[-] CRITICAL: Node P{msg.sender} submitted "
                    "an INVALID share during reconstruction!"
                )
                print(
                    "[!] SECURITY ABORT: Reconstruction canceled "
                    "due to malicious activity."
                )
                return

            shares.append((msg.sender, msg.share))

        if len(shares) < self.t:
            print(
                f"[-] Reconstruction failed: received {len(shares)} "
                f"valid shares, but {self.t} are required."
            )
            return

        secret = self.vss.reconstruct(shares)

        print(
            f"[=] Execution Output -> Recovered Field Element: "
            f"{secret} | Original: {self.secret}"
        )

        def demonstrate_high_degree_attack(self):
            print("\n[ATTACK DEMO] Evaluating node processing states post distribution...")
            all_aborted = all(not p.valid for p in self.participants.values())
            if all_aborted:
                print("[+] SUCCESS: Honest nodes caught the inflated threshold array bound and aborted uniformly.")
            else:
                print("[-] FAILURE: Active processing nodes accepted the overflowed polynomial degree.")

    def run(self):
        while True:
            cmd = input("\nCommands (add / refresh / reconstruct / attack / exit): ").strip().lower()
            if cmd == "exit":
                break
            elif cmd == "add":
                self.metrics.start_timer("ADD_TOTAL")
                self.add()
                self.metrics.stop_timer("ADD_TOTAL")
                self.metrics.report()

            elif cmd == "refresh":
                self.metrics.start_timer("REFRESH_TOTAL")
                self.refresh()
                self.metrics.stop_timer("REFRESH_TOTAL")
                self.metrics.report()
            elif cmd == "reconstruct":
                self.metrics.start_timer("RECONSTRUCTION_TOTAL")
                self.reconstruct()
                self.metrics.stop_timer("RECONSTRUCTION_TOTAL")
                self.metrics.report()
            elif cmd == "attack":
                print("\nChoose Adversarial Routine:")
                print("1: Malicious Dealer (Poisoned ZKP Proof)")
                print("2: Malicious Dealer (Poisoned Commitments)")
                print("3: Active Node sends dirty subshares during Refresh step")
                print("4: Active Node sabotages dynamic Participant Addition")
                print("5: Active Node lies during Secret Reconstruction phase")
                print("6: Malicious Dealer (Higher Polynomial Degree Attack)")
                choice = input("Select (1-6): ").strip()
                
                if choice == "1":
                    engine = FeldmanVSSProtocol(self.n, self.t, self.secret)
                    engine.dealer.mode = MaliciousMode.EVIL_DEALER_BAD_PROOF
                    engine.setup()
                elif choice == "2":
                    engine = FeldmanVSSProtocol(self.n, self.t, self.secret)
                    engine.dealer.mode = MaliciousMode.EVIL_DEALER_BAD_COMMITMENT
                    engine.setup()
                elif choice == "3":
                    self.refresh(attacker_id=1)
                elif choice == "4":
                    self.add(attacker_id=1)
                elif choice == "5":
                    self.reconstruct(liar_id=1)
                elif choice == "6":
                    engine = FeldmanVSSProtocol(self.n, self.t, self.secret)
                    engine.dealer.mode = MaliciousMode.EVIL_DEALER_HIGH_DEGREE
                    engine.setup()
                    engine.demonstrate_high_degree_attack()
            else:
                print("Unknown execution command.")

if __name__ == "__main__":
    protocol = FeldmanVSSProtocol(n=10, t=5, secret=420)
    protocol.run()