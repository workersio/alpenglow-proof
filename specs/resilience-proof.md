# Alpenglow Resilience — Lemmas/Corollary/Theorem (Whitepaper Numbering)

This document lists the **exact whitepaper-numbered lemmas** you need for the three resilience properties, plus one corollary (also numbered in the whitepaper), and a final combined **Resilience Theorem**. The statements are phrased to match the paper’s definitions and to be usable as references in TLAPS proofs.  
Whitepaper sources (numbers and wording) match the uploaded `alpenglow-whitepaper.md`.

---

## Property A — Safety maintained with ≤20% Byzantine stake

### **Lemma 20** (notarization or skip).
A correct node **exclusively** casts only one vote per slot: either a notarization vote for some block in that slot or a skip vote for that slot (but not both).

### **Lemma 23.**
If correct nodes with **more than 40%** of stake cast notarization votes for the **same** block \\(b\\) in slot \\(s\\), then **no other block** can be notarized in slot \\(s\\).

### **Lemma 24.**
At most **one** block can be notarized in a given slot.

### **Lemma 25.**
If a block is **finalized** by a correct node, the block is also **notarized**.

### **Lemma 31.**
Suppose some correct node finalizes a block \\(b_i\\) and some (possibly different) correct node finalizes a block \\(b_k\\) where \\(\\text{slot}(b_k) \\ge \\text{slot}(b_i)\\). Then \\(b_k\\) is a **descendant** of \\(b_i\\).

### **Lemma 32.**
Suppose some correct node finalizes a block \\(b_i\\) and correct nodes subsequently finalize blocks \\(b\\) in later slots. Then any later finalized block \\(b\\) is a **descendant** of \\(b_i\\).

> **How these imply safety under ≤20% Byzantine:** Lemmas 20/23/24 ensure **single notarization per slot** by honest non-equivocation and quorum intersection; Lemma 25 lifts finalized ⇒ notarized; Lemmas 31/32 give **descendant-only** growth of finalized blocks. Together they yield Theorem 1 (safety).

---

## Property B — Liveness maintained with ≤20% non-responsive stake

*(Post-GST partial synchrony and a fair leader schedule are assumed, as in the whitepaper.)*

### **Lemma 7** (rotor resilience).
If the leader is correct and the relay selection meets the paper’s conditions, Rotor **succeeds** with high probability.

### **Lemma 8** (rotor latency).
**Conditioned on Rotor success**, a broadcast at time \\(t\\) reaches at least a \\(q\\)-stake set by time \\(t + \\delta_q\\) for \\(q \\in \\{60\\%, 80\\%\\}\\).

### **Lemma 33.**
If a correct node emits `ParentReady(s, hash(b))`, then for **every** slot \\(k\\) in the window beginning at \\(s\\), the node emits `Timeout(k)`.

### **Corollary 34.**
If a node sets a **timeout** for slot \\(s\\), it has **already** set timeouts for all earlier slots in the same leader window.

### **Lemma 35.**
If **all** correct nodes set the timeout for slot \\(s\\), then **every** correct node will cast either a **notarization** vote or a **skip** vote in slot \\(s\\).

### **Lemma 36.**
If **no** set of correct nodes with more than **40%** of stake cast notarization votes in slot \\(s\\), **no** correct node will add the terminal marker `ItsOver` to state\\([s]\\).

### **Lemma 37.**
If **all** correct nodes set the timeout for slot \\(s\\), then correct nodes with **more than 40%** stake cast **notarization votes for the same block** in slot \\(s\\).

### **Lemma 38.**
If correct nodes with more than **40%** stake cast notarization votes for block \\(b\\) in slot \\(s\\), then correct nodes will observe a **notar-fallback certificate** for \\(b\\) (if a full notar is not yet formed).

### **Lemma 39.**
If **all** correct nodes set the timeouts for the slots in a leader window and Rotor is successful for that window, then for **each** slot \\(s'\\) in the window correct nodes observe **either** a notarization certificate for some block \\(b\\) with \\(s' = \\text{slot}(b)\\), **or** a **skip** certificate for \\(s'\\).

### **Lemma 40.**
If **all** correct nodes set timeouts for a window starting at slot \\(s\\), then correct nodes **emit `ParentReady` for the next window** starting at \\(s^+ > s\\).

### **Lemma 41.**
**All** correct nodes will set the **timeouts for all slots** (induction over windows).

### **Lemma 42.**
After GST, if the **first** correct node observes a **notarization** in the active window at time \\(t\\), then **all** correct nodes will set timeouts for that window by time \\(t + \\Delta\\).

> **How these imply liveness with ≤20% non-responsive:** With ≤20% non-responsive stake we have ≥80% responsive; Lemmas 7–8 provide the \\(\\delta\\)-quantile dissemination; Lemmas 33–42 guarantee **per-slot progress** (vote or skip) and rolling windows. Hence Theorem 2 (liveness) holds and finalization continues (fast when ≥80% responsive is met; otherwise slow with two \\(\\delta_{60}\\) steps).

---

## Property C — Network partition recovery guarantees

*(The whitepaper does not assign specific lemma numbers to “partition recovery.” It follows by combining safety (Theorem 1) with liveness (Theorem 2) once the network heals.)*

### Derived Corollary (from **Theorem 1** and **Theorem 2**).
For any **finite** partition interval, upon healing (post-GST):  
(i) previously finalized blocks remain **safe** (no conflicting finalization due to Theorem 1);  
(ii) the system **converges** as certificates disseminate; and  
(iii) **liveness resumes** with the same time bounds (by Theorem 2 and Lemmas 7–8, 33–42).

> This corollary is *derived*—it does not have a whitepaper lemma number. If you need a numbered reference, cite **Theorem 1** (safety) and **Theorem 2** (liveness) directly.

---

## Final Resilience Theorem (Combined)

- **Theorem 1 (safety)** — *whitepaper number preserved*  
  If any correct node finalizes a block \\(b\\) in slot \\(s\\), then for any block \\(b'\\) finalized in any slot \\(s' \\ge s\\), \\(b'\\) is a **descendant** of \\(b\\).  
  *(Uses Lemmas 25, 31, 32; relies on Lemmas 20, 23, 24 to exclude conflicting notarizations.)*

- **Theorem 2 (liveness)** — *whitepaper number preserved*  
  Let \\(v_\\ell\\) be a correct leader of a window starting at slot \\(s\\). After GST, if Rotor is successful for all slots in that window and timeouts are set (per Lemmas 33–42), then **every** block proposed by correct nodes in \\(\\text{WINDOWSLOTS}(s)\\) will be **finalized** by all correct nodes.  
  *(Uses Lemmas 7–8, 33–42; yields fast/slow bounds via \\(\\delta_{80}\\), \\(\\delta_{60}\\).)*

These two theorems together provide the **resilience guarantees** requested: safety with ≤20% Byzantine stake, liveness with ≤20% non-responsive stake, and recovery after partitions once the network heals.
