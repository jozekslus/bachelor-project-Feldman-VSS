
import secrets
import hashlib
from enum import Enum, auto
from dataclasses import dataclass
import time
from typing import Dict, List, Tuple
from ecpy.curves import Curve


# ============================================================
# Curve Setup
# ============================================================
curve = Curve.get_curve("secp256k1")
G = curve.generator
ORDER = curve.order

class ProtocolState(Enum):
    PHASE_1_HASHES = auto()
    PHASE_2_REVEALS = auto()
    PHASE_3_COMPLETE = auto()
    ABORTED = auto()

# ============================================================
# Pure P2P Message Types 
# ============================================================
@dataclass
class HashCommitmentMessage:
    sender: int
    receiver: int
    commitment_hash: bytes

@dataclass
class HashBroadcastMessage:
    sender: int
    receiver: int
    hash_board: Dict[int, bytes]  # Mapping of participant IDs to their commitment hashes

@dataclass
class DkgRevealMessage:
    sender: int
    receiver: int
    commitments: list       # EC Points (M_i,k)
    share: int              # P2P evaluation f_i(receiver)
    fischlin_proofs: list   # List of Fischlin proofs for each coefficient


@dataclass
class ReconstructionShareMessage:
    sender: int
    receiver: int
    share: int



# ============================================================
# Network Engine (Asynchronous Message Router)
# ============================================================
class Network:
    def __init__(self):
        self.abort_time = None
        self.queues = {}
        self.aborted = False
        self.counter = 0

    def register(self, pid):
        self.queues[pid] = []

    def send(self, msg):
        if not self.aborted:
            self.queues[msg.receiver].append(msg)
            self.counter += 1

    def recv_all(self, pid):
        if self.aborted:
            return []
        msgs = self.queues[pid]
        self.queues[pid] = []
        return msgs

    def trigger_global_abort(self, sender_id: int, reason: str):
        self.aborted = True
        print(f"\n[!!!] NETWORK-WIDE ABORT TRIGGERED BY P{sender_id} [!!!]")
        print(f"[!] Reason: {reason}")
        print(f"time to detect abort: {(self.abort_time - time.perf_counter()) * 1000:.2f} ms")

# ============================================================
# Fischlin-Schnorr Non-Interactive Proof of Knowledge
# ============================================================
class FischlinSchnorrOfficial:
    def __init__(self, G, order, rho=16, b=8, challenge_bits=6):
        self.G = G
        self.order = order
        self.rho = rho                  # Total parallel repetitions
        self.b = b                      # Hardness bit parameter (target zeros)
        self.challenge_bits = challenge_bits
        self.max_challenge = 1 << challenge_bits

    def encode_point(self, P):
        if P.is_infinity: return b"INF"
        return f"{P.x}|{P.y}".encode()

    def H_full(self, x_point, commitments, sid=b""):
        data = sid + self.encode_point(x_point)
        for m_i in commitments:
            data += self.encode_point(m_i)
        return hashlib.sha256(data).digest()

    def H_b(self, common_h, i, e_i, z_i):
        data = (
            common_h + 
            i.to_bytes(4, "big") + 
            e_i.to_bytes((self.challenge_bits + 7) // 8, "big") + 
            z_i.to_bytes((self.order.bit_length() + 7) // 8, "big")
        )
        h = int.from_bytes(hashlib.sha256(data).digest(), "big")
        return h & ((1 << self.b) - 1)

    def prove_single(self, X, x, sid=b""):
        while True:
            m_vec = []
            sigma_vec = []
            for _ in range(self.rho):
                r = secrets.randbelow(self.order)
                m_vec.append(r * self.G)
                sigma_vec.append(r)

            common_h = self.H_full(X, m_vec, sid)
            e_vec = [0] * self.rho
            z_vec = [0] * self.rho
            proof_failed = False

            for i in range(self.rho):
                success_in_round = False
                for e_i in range(self.max_challenge):
                    z_i = (sigma_vec[i] + e_i * x) % self.order
                    h_i = self.H_b(common_h, i, e_i, z_i)
                    
                    if h_i == 0:
                        e_vec[i] = e_i
                        z_vec[i] = z_i
                        success_in_round = True
                        break
                
                if not success_in_round:
                    proof_failed = True
                    break 

            if not proof_failed:
                return {"m": m_vec, "e": e_vec, "z": z_vec}

    def verify_single(self, X, proof, sid=b""):
        m_vec, e_vec, z_vec = proof["m"], proof["e"], proof["z"]
        if len(m_vec) != self.rho or len(e_vec) != self.rho or len(z_vec) != self.rho:
            return False

        common_h = self.H_full(X, m_vec, sid)
        for i in range(self.rho):
            if z_vec[i] * self.G != m_vec[i] + e_vec[i] * X: return False
            if self.H_b(common_h, i, e_vec[i], z_vec[i]) != 0: return False
        return True

# ============================================================
# Feldman VSS Engine Core
# ============================================================
class FeldmanVSSEngine:
    def __init__(self, t: int):
        self.t = t
        self.G = G
        self.order = ORDER

    def verify_share(self, share, commitments, pid):
        if len(commitments) != self.t:
            return False
        left = share * self.G
        right = None
        for k in range(self.t):
            term = pow(pid, k, self.order) * commitments[k]
            right = term if right is None else right + term
        return left == right

# ============================================================
# Joint Feldman Participant  (Phase-Synchronous Protocol Participant)
# ============================================================
class DkgParticipant:
    def __init__(self, pid: int, n: int, t: int, network: Network, original_n: int ):
        self.pid = pid
        self.n = n
        self.original_n = n
        self.t = t
        self.network = network
        self.fischlin = FischlinSchnorrOfficial(G, ORDER, rho=8, b=6, challenge_bits=6)
        self.vss = FeldmanVSSEngine(t)
        
        # Local Setup Contributions
        self.local_secret = secrets.randbelow(ORDER)
        self.local_polynomial = self._gen_poly(self.local_secret)
        self.local_commitments = [c * G for c in self.local_polynomial]
        
        # Temporary runtime memory buffers for Lifecycle Resets
        self.current_refresh_poly = []
        self.current_refresh_commits = []
        self.refresh_hash_board: Dict[int, bytes] = {}  
        
        # Asynchronous State Registries
        self.peer_ids = [i for i in range(1, n + 1)]
        self.hash_bulletin_board: Dict[int, bytes] = {}
        self.received_commitments: Dict[int, list] = {}
        self.received_shares: Dict[int, int] = {}
        
        # Outputs
        self.final_private_share = None
        self.final_joint_public_key = None
        self.status = ProtocolState.PHASE_1_HASHES

    def _gen_poly(self, secret):
        return [secret] + [secrets.randbelow(ORDER) for _ in range(self.t - 1)]

    def _eval_poly(self, coeffs, x):
        y = 0
        for c in reversed(coeffs): y = (y * x + c) % ORDER
        return y

    def _encode_point_safely(self, pt) -> bytes:
        """Helper to serialize points, explicitly handling the Point at Infinity."""
        if pt.is_infinity:
            return b"INF"
        return f"{pt.x}|{pt.y}".encode()

    def compute_commitment_hash(self) -> bytes:
        data = b""
        for point in self.local_commitments:
            data += self._encode_point_safely(point)
        return hashlib.sha256(data).digest()

    # --------------------------------------------------------
    # P2P ROUND 1: Commit Phase
    # --------------------------------------------------------
    def send_phase1_hashes(self):
        my_hash = self.compute_commitment_hash()
        self.hash_bulletin_board[self.pid] = my_hash
        for peer_id in self.peer_ids:
            if peer_id == self.pid: continue
            self.network.send(HashCommitmentMessage(self.pid, peer_id, my_hash))

    def receive_phase1_hashes(self):
        incoming = self.network.recv_all(self.pid)
        for msg in incoming:
            if isinstance(msg, HashCommitmentMessage):
                self.hash_bulletin_board[msg.sender] = msg.commitment_hash

        if len(self.hash_bulletin_board) != self.n:
            self.status = ProtocolState.ABORTED
            self.network.trigger_global_abort(self.pid, "Missing cryptographic commitments during lock-in round.")
        else:
            self.status = ProtocolState.PHASE_2_REVEALS

    def hash_broadcast(self): 
        for peer_id in self.peer_ids:
            if peer_id == self.pid: continue 
            self.network.send(HashBroadcastMessage(self.pid,peer_id, self.hash_bulletin_board ))

    def verify_broadcast(self) :
        incoming = self.network.recv_all(self.pid)
        for msg in incoming:
            if isinstance(msg, HashBroadcastMessage):
                for pid, hash_val in msg.hash_board.items():
                    if pid not in self.hash_bulletin_board:
                        self.status = ProtocolState.ABORTED
                        self.network.trigger_global_abort(self.pid, f"Missing commitment hash from P{pid} in broadcast.")
                        return
                    if self.hash_bulletin_board[pid] != hash_val:
                        self.status = ProtocolState.ABORTED
                        self.network.trigger_global_abort(self.pid, f"Commitment hash mismatch for P{pid} in broadcast.")
                        return
    # --------------------------------------------------------
    # P2P ROUND 2: Reveal & Verify Phase
    # --------------------------------------------------------
    def send_phase2_reveals(self):
        if self.status == ProtocolState.ABORTED: return
        
        proofs = []
        for idx, coeff in enumerate(self.local_polynomial):
            tag = f"P_{self.pid}_COEFF_{idx}".encode()
            X_point = self.local_commitments[idx]
            proofs.append(self.fischlin.prove_single(X_point, coeff, tag))
        
        for peer_id in self.peer_ids:
            if peer_id == self.pid: continue
            peer_share = self._eval_poly(self.local_polynomial, peer_id)
            self.network.send(DkgRevealMessage(
                sender=self.pid, receiver=peer_id, commitments=self.local_commitments,
                share=peer_share, fischlin_proofs=proofs
            ))
            
        self.received_commitments[self.pid] = self.local_commitments
        self.received_shares[self.pid] = self._eval_poly(self.local_polynomial, self.pid)

    def receive_and_verify_phase2(self):
        if self.status == ProtocolState.ABORTED: return
        
        incoming = self.network.recv_all(self.pid)
        for msg in incoming:
            if isinstance(msg, DkgRevealMessage):
                # 1. Commitment Binding Check
                data = b""
                for pt in msg.commitments: data += f"{pt.x}|{pt.y}".encode()
                if hashlib.sha256(data).digest() != self.hash_bulletin_board.get(msg.sender):
                    self.status = ProtocolState.ABORTED
                    self.network.trigger_global_abort(self.pid, f"Rushing Attack detected! P{msg.sender} shifted parameters.")
                    return

                # 2. Threshold Struct validation
                if len(msg.commitments) != self.t:
                    self.status = ProtocolState.ABORTED
                    self.network.trigger_global_abort(self.pid, f"Degree bounds breach from P{msg.sender}.")
                    return

                # 3. Batch Fischlin Proof Verification
                for idx, point in enumerate(msg.commitments):
                    tag = f"P_{msg.sender}_COEFF_{idx}".encode()
                    if not self.fischlin.verify_single(point, msg.fischlin_proofs[idx], tag):
                        self.status = ProtocolState.ABORTED
                        self.network.trigger_global_abort(self.pid, f"Fischlin validation failed for P{msg.sender}")
                        return

                # 4. Feldman Evaluation check
                if not self.vss.verify_share(msg.share, msg.commitments, self.pid):
                    self.status = ProtocolState.ABORTED
                    self.network.trigger_global_abort(self.pid, f"Feldman algebraic validation failed for P{msg.sender}")
                    return

                self.received_commitments[msg.sender] = msg.commitments
                self.received_shares[msg.sender] = msg.share

        if len(self.received_shares) != self.n:
            self.status = ProtocolState.ABORTED
            self.network.trigger_global_abort(self.pid, "Incomplete multi-party transmission payload channels.")
        else:
            self.status = ProtocolState.PHASE_3_COMPLETE

    def aggregate_keys(self):
        if self.status == ProtocolState.ABORTED: return
        self.final_private_share = sum(self.received_shares.values()) % ORDER
        
        joint_key = None
        for pid in self.received_commitments:
            base_point = self.received_commitments[pid][0]
            joint_key = base_point if joint_key is None else joint_key + base_point
        self.final_joint_public_key = joint_key

 

# ============================================================
# Dynamic Global P2P Reconstruction Function
# ============================================================
def simulate_p2p_reconstruction(nodes: Dict[int, DkgParticipant], network: Network, target_node_id: int, threshold_t: int):
    if network.aborted:
        print("\n[-] Network is in an aborted state. Cannot reconstruct.")
        return

    print(f"\n=== P2P RECONSTRUCTION: Gathering Reconstruction Shares at Node P{target_node_id} ===")
    committee_ids = list(nodes.keys())[:threshold_t]
    
    for pid in committee_ids:
        # Check if node has actually completed their setup routines
        if nodes[pid].final_private_share is not None:
            share_payload = nodes[pid].final_private_share
            network.send(ReconstructionShareMessage(sender=pid, receiver=target_node_id, share=share_payload))
        
    target_node = nodes[target_node_id]
    incoming_msgs = network.recv_all(target_node_id)
    
    shares_for_interpolation = []
    for msg in incoming_msgs:
        if isinstance(msg, ReconstructionShareMessage):
            # Compute global aggregated commitment matrix dynamically
            global_commitments = []
            for k in range(threshold_t):
                term = None
                for node_id in target_node.received_commitments:
                    val = target_node.received_commitments[node_id][k]
                    term = val if term is None else term + val
                global_commitments.append(term)
                
            if not target_node.vss.verify_share(msg.share, global_commitments, msg.sender):
                network.trigger_global_abort(target_node_id, f"Verification failed for reconstruction share from P{msg.sender}!")
                return
                
            shares_for_interpolation.append((msg.sender, msg.share))

    def inv(a): return pow(int(a), -1, ORDER)
    recovered_secret = 0
    for i, (xi, yi) in enumerate(shares_for_interpolation):
        li = 1
        for j, (xj, _) in enumerate(shares_for_interpolation):
            if i != j:
                li = (li * (0 - xj) * inv(xi - xj)) % ORDER
        recovered_secret = (recovered_secret + yi * li) % ORDER

    actual_master_secret = sum(p.local_secret for p in nodes.values() if p.pid <= p.original_n) % ORDER # Exclude new nodes (passive recipients)
    print(f"[=] Interpolated Secret Intercept: {recovered_secret}")
    print(f"[=] Expected Sum of Local Secrets: {actual_master_secret}")
    
    if recovered_secret == actual_master_secret :
        print("[+] MATCH: Joint Private Key verification successful.")


###    MALICOUS PARTICIPANTS   ###
class MaliciousShareParticipant(DkgParticipant):
    def send_phase2_reveals(self):
        if self.status == ProtocolState.ABORTED:
            return

        proofs = []
        for idx, coeff in enumerate(self.local_polynomial):
            tag = f"P_{self.pid}_COEFF_{idx}".encode()
            proofs.append(
                self.fischlin.prove_single(
                    self.local_commitments[idx],
                    coeff,
                    tag
                )
            )

        for peer_id in self.peer_ids:
            if peer_id == self.pid:
                continue

            share = self._eval_poly(self.local_polynomial, peer_id)

            # Corrupt the share
            share = (share + 12345) % ORDER

            self.network.send(
                DkgRevealMessage(
                    sender=self.pid,
                    receiver=peer_id,
                    commitments=self.local_commitments,
                    share=share,
                    fischlin_proofs=proofs
                )
            )
        self.received_commitments[self.pid] = self.local_commitments
        self.received_shares[self.pid] = self._eval_poly(self.local_polynomial, self.pid)



        
class MaliciousRushingParticipant(DkgParticipant):
    def send_phase2_reveals(self):
        if self.status == ProtocolState.ABORTED: return

        #attack : changing the commitment 
        self.local_commitments[0] = secrets.randbelow(ORDER) * G
        
        proofs = []
        for idx, coeff in enumerate(self.local_polynomial):
            tag = f"P_{self.pid}_COEFF_{idx}".encode()
            X_point = self.local_commitments[idx]
            proofs.append(self.fischlin.prove_single(X_point, coeff, tag))
        
        for peer_id in self.peer_ids:
            if peer_id == self.pid: continue
            peer_share = self._eval_poly(self.local_polynomial, peer_id)
            self.network.send(DkgRevealMessage(
                sender=self.pid, receiver=peer_id, commitments=self.local_commitments,
                share=peer_share, fischlin_proofs=proofs
            ))
            
        self.received_commitments[self.pid] = self.local_commitments
        self.received_shares[self.pid] = self._eval_poly(self.local_polynomial, self.pid)

class MalicousFischlinParticipant(DkgParticipant):
 
    def send_phase2_reveals(self):
        if self.status == ProtocolState.ABORTED: return
        
        proofs = []
        for idx, coeff in enumerate(self.local_polynomial):
            tag = f"P_{self.pid}_COEFF_{idx}".encode()
            X_point = self.local_commitments[idx]
            proofs.append(self.fischlin.prove_single(X_point, coeff, tag))
        #sending a garbage proof 
        proofs[0]["z"][0] = (proofs[0]["z"][0] + 1) % ORDER
        
        for peer_id in self.peer_ids:
            if peer_id == self.pid: continue
            peer_share = self._eval_poly(self.local_polynomial, peer_id)
            self.network.send(DkgRevealMessage(
                sender=self.pid, receiver=peer_id, commitments=self.local_commitments,
                share=peer_share, fischlin_proofs=proofs
            ))
            
        self.received_commitments[self.pid] = self.local_commitments
        self.received_shares[self.pid] = self._eval_poly(self.local_polynomial, self.pid)


class SilentParticipant(DkgParticipant):
    def send_phase1_hashes(self):
        pass


class MalicousReconstructionShareParticipant(DkgParticipant):
    def aggregate_keys(self):
        if self.status == ProtocolState.ABORTED: return
        self.final_private_share = sum(self.received_shares.values()) % ORDER
        
        joint_key = None
        for pid in self.received_commitments:
            base_point = self.received_commitments[pid][0]
            joint_key = base_point if joint_key is None else joint_key + base_point
        self.final_joint_public_key = joint_key
        self.final_private_share = (self.final_private_share + 12345) % ORDER  # Corrupt the final private share



# ============================================================
# Main Protocol Execution Flow
# ============================================================
if __name__ == "__main__":
    print("\n=== DECENTRALIZED P2P DKG SIMULATION ===")
    print("input n = number of participants, t = threshold for reconstruction :: ")
    n = int(input("Enter n (total participants): "))
    t = int(input("Enter t (threshold): "))
    network = Network()
    nodes = {}

    for pid in range(1, n + 1):
        network.register(pid)
        nodes[pid] = DkgParticipant(pid, n, t, network, original_n=n)


    while True:
        print("\n=== SIMULATION MENU ===")
        print("1. Run Joint Key Generation Phase")
        print("2. Check Key Aggregation and Reconstruction")
        print("3. Run Malicious Attack Simulation")
        print("4. Reset Attacks")
        print("5. Exit Simulation")
        choice = input("Select an option (1-5): ")

        if choice == '1':
            start_time = time.perf_counter()
            network.abort_time = time.perf_counter()
            print("=== STEP 1: Core P2P Distributed Key Generation ===")
            for node in nodes.values(): node.send_phase1_hashes()
            for node in nodes.values(): node.receive_phase1_hashes()
            for node in nodes.values(): node.hash_broadcast()
            for node in nodes.values(): node.verify_broadcast()
            for node in nodes.values(): node.send_phase2_reveals()
            for node in nodes.values(): node.receive_and_verify_phase2()
            for node in nodes.values(): node.aggregate_keys()

            print("\n=== STEP 1 COMPLETE: Joint Key Generation Phase ===")

            print("total number of messages sent in the network: ", network.counter)
            end_time = time.perf_counter()
            elapsed_time_ms = (end_time - start_time) * 1000
            print(f"Elapsed time: {elapsed_time_ms:.2f} ms")

        if choice == '2':
            start_time = time.perf_counter()
            print("\n=== STEP 2: Verifying Key Aggregation and Reconstruction ===")
            simulate_p2p_reconstruction(nodes, network, target_node_id=1, threshold_t=t)
            print("\n=== STEP 2 COMPLETE: Key Aggregation and Reconstruction Phase ===")
            end_time = time.perf_counter()
            elapsed_time_ms = (end_time - start_time) * 1000
            print(f"Elapsed time: {elapsed_time_ms:.2f} ms")
        
        if choice == '3':
            print("\n=== STEP 3: Malicious Attack Simulation ===")
            print("\nChoose your attack scenario: " )
            print("\n1. Malicious SubShare Participant ")
            print("\n2. Malicious Rushing Participant ")
            print("\n3. Malicious Fischlin Proof Participant ")
            print("\n4. Silent Participant (No Participation) ")
            print("\n5. Malicious Reconstruction Share Participant ")
            attack_choice = input("Select an attack scenario (1-6): ")
            if attack_choice == '1':
                nodes[1] = MaliciousShareParticipant(1, n, t, network, original_n=n)
            elif attack_choice == '2':
                nodes[1] = MaliciousRushingParticipant(1, n, t, network, original_n=n)   
            elif attack_choice == '3':
                nodes[1] = MalicousFischlinParticipant(1, n, t, network, original_n=n)
            elif attack_choice == '4':
                nodes[1] = SilentParticipant(1, n, t, network, original_n=n)    
            elif attack_choice == '5':  
                nodes[1] = MalicousReconstructionShareParticipant(1, n, t, network, original_n=n)
            else:   
                print("Invalid attack scenario choice. Returning to main menu.")
                continue
            continue
        if choice == '4':
            print("\n=== STEP 4: Resetting Attacks ===")
            nodes[1] = DkgParticipant(1, n, t, network, original_n=n)
            print("Node P1 has been reset to a standard participant.")
            network.aborted = False
            network.counter = 0
            time.perf_counter()
            for pid in network.queues:
                network.queues[pid].clear()
            continue


        if choice == '5':
            print("\n=== EXITING SIMULATION ===")
            break
