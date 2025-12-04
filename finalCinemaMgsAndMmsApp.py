# CinemaMgsAndMmsApp.py
import math
import random
from decimal import Decimal, localcontext
import tkinter as tk
from tkinter import ttk, messagebox, END, BOTH, X, Y, HORIZONTAL, VERTICAL, LEFT, RIGHT
import ttkbootstrap as tb
from ttkbootstrap.constants import *
import matplotlib.pyplot as plt
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
from statistics import mean

# repeatable runs for debugging; remove or change seed if you want randomness each run
random.seed(0)

# --------------------------
# Arrival / service / priority generation
# --------------------------
def generate_arrivals_by_cp(mean_arrival):
    cumulative = 0.0
    cp = []
    k = 0
    # build Poisson cumulative distribution until near 1
    while cumulative < 0.99999:
        with localcontext() as ctx:
            ctx.prec = 20
            prob = (Decimal(math.exp(-mean_arrival)) *
                    ctx.power(Decimal(mean_arrival), k)) / math.factorial(k)
            cumulative += float(prob)
            cp.append(float(cumulative))
        k += 1

    n = len(cp)
    cp_lookup = [0.0] + cp[:-1]
    avg_times = list(range(n))

    inter_arrivals = []
    for _ in range(n):
        r = random.random()
        for kk, cval in enumerate(cp):
            if r <= cval:
                inter_arrivals.append(kk)
                break

    if inter_arrivals:
        inter_arrivals[0] = 0

    arrival_times = [inter_arrivals[0]]
    for i in range(1, n):
        arrival_times.append(arrival_times[i - 1] + inter_arrivals[i])

    return cp, cp_lookup, avg_times, inter_arrivals, arrival_times


def generate_service_times(n, mean_service, dist_type="normal", a=None, b=None):
    """General service time generator for M/G/s.
    dist_type in {"normal","uniform","lognormal","gamma","exponential"}.
    All outputs are integer >=1.
    If dist_type == "uniform", the formula used is:
        service = a + (b - a) * r
    where r = random.random().
    If a or b are None for uniform, fallback to uniform around mean (50%-150%).
    """
    out = []
    for _ in range(n):
        if mean_service is not None and mean_service <= 0:
            out.append(1)
        else:
            if dist_type == "normal":
                # Normal with std = mean/3 (so most mass near mean); avoid <=0
                base_mean = mean_service if mean_service is not None else 1.0
                v = max(0.1, random.gauss(base_mean, max(0.001, base_mean / 3.0)))
            elif dist_type == "uniform":
                # Use user's requested formula a + (b - a) * r when a and b provided.
                if a is not None and b is not None:
                    # produce a continuous value in [a, b)
                    v = a + (b - a) * random.random()
                else:
                    # fallback: uniform around mean ±50%
                    base_mean = mean_service if mean_service is not None else 1.0
                    v = random.uniform(0.5 * base_mean, 1.5 * base_mean)
            elif dist_type == "lognormal":
                # lognormal constructed to have approximate mean_service
                sigma = 0.6
                base_mean = mean_service if mean_service is not None else 1.0
                mu = math.log(max(1e-6, base_mean)) - 0.5 * sigma ** 2
                v = random.lognormvariate(mu, sigma)
            elif dist_type == "gamma":
                # gamma with shape=2 gives moderate skew; scale chosen to match mean
                shape = 2.0
                base_mean = mean_service if mean_service is not None else 1.0
                scale = base_mean / shape
                v = random.gammavariate(shape, max(1e-6, scale))
            else:
                # exponential (M/M/s behavior) -- random.expovariate expects rate = 1/mean
                base_mean = mean_service if mean_service is not None else 1.0
                v = random.expovariate(1.0 / base_mean)

            out.append(max(1, int(round(v))))
    return out


def generate_priorities(n, low=1, high=3):
    return [random.randint(low, high) for _ in range(n)]


# --------------------------
# Patient class
# --------------------------
class Patient:
    def __init__(self, pid, arrival, service, priority=None):
        self.id = pid
        self.arrival = int(arrival)
        self.service = int(service)
        self.remaining = int(service)
        self.priority = int(priority) if priority is not None else None
        self.first_start = None
        self.end = None
        self.turnaround = None
        self.wait = None
        self.response = None
        self.preferred_server = None
        self.segments = []

    def start_on(self, server_id, t):
        t = int(t)
        if self.first_start is None:
            self.first_start = t
            self.response = t - self.arrival
        self.segments.append([server_id, t, None])
        self.preferred_server = None

    def stop_at(self, t):
        t = int(t)
        if self.segments and self.segments[-1][2] is None:
            self.segments[-1][2] = t

    def finalize(self, t):
        t = int(t)
        self.end = t
        self.turnaround = self.end - self.arrival
        self.wait = max(0, self.turnaround - self.service)
        if self.response is None:
            self.response = 0
# --------------------------
# Simulators
# --------------------------
def simulate_preemptive_v5(mean_arrival, mean_service, servers_count=1, pr_range=(1, 3), dist_type="normal", a=None, b=None):
    cp, cp_lookup, avg_times, inter_arr, arrivals = generate_arrivals_by_cp(mean_arrival)
    n = len(arrivals)
    services = generate_service_times(n, mean_service, dist_type, a=a, b=b)
    priorities = generate_priorities(n, pr_range[0], pr_range[1])

    patients = [Patient(i + 1, arrivals[i], services[i], priorities[i]) for i in range(n)]

    servers = [{'p': None, 'end': None} for _ in range(servers_count)]
    waiting = []

    arrival_idx = 0

    # For plotting
    timeline = []
    queue_lengths = []
    util_over_time = []

    def next_arrival_time():
        return patients[arrival_idx].arrival if arrival_idx < n else math.inf

    def next_completion_time():
        times = [s['end'] for s in servers if s['p'] is not None]
        return min(times) if times else math.inf

    while True:
        ta = next_arrival_time()
        tc = next_completion_time()
        if ta == tc == math.inf:
            break

        if ta <= tc:
            t = ta
            arrivals_at_t = []
            while arrival_idx < n and patients[arrival_idx].arrival == t:
                arrivals_at_t.append(patients[arrival_idx])
                arrival_idx += 1

            # arrivals at same time sorted by priority, arrival, id
            arrivals_at_t.sort(key=lambda p: (p.priority, p.arrival, p.id))

            for newp in arrivals_at_t:
                # check if any running has worse (higher numeric) priority than new arrival
                candidate_sid = None
                worst_priority = -math.inf
                for sid, s in enumerate(servers):
                    if s['p'] is not None and s['p'].priority > newp.priority:
                        if s['p'].priority > worst_priority:
                            worst_priority = s['p'].priority
                            candidate_sid = sid

                if candidate_sid is not None:
                    # preempt the worst running
                    running = servers[candidate_sid]['p']
                    running.stop_at(t)
                    seg_start = running.segments[-1][1]
                    consumed = int(t) - int(seg_start)
                    running.remaining = max(0, running.remaining - consumed)
                    running.preferred_server = candidate_sid + 1
                    if running.remaining > 0:
                        waiting.append(running)
                    servers[candidate_sid] = {'p': None, 'end': None}
                    newp.start_on(candidate_sid + 1, t)
                    servers[candidate_sid]['p'] = newp
                    servers[candidate_sid]['end'] = t + newp.remaining
                else:
                    free_sid = next((sid for sid, s in enumerate(servers) if s['p'] is None), None)
                    if free_sid is not None:
                        newp.start_on(free_sid + 1, t)
                        servers[free_sid]['p'] = newp
                        servers[free_sid]['end'] = t + newp.remaining
                    else:
                        waiting.append(newp)

            # after arrivals, try to fill any free servers from waiting queue (consider preferred_server)
            assigned = True
            while assigned:
                assigned = False
                for sid, s in enumerate(servers):
                    if s['p'] is None and waiting:
                        pref_cands = [p for p in waiting if p.preferred_server == sid + 1]
                        if pref_cands:
                            pref_cands.sort(key=lambda p: (p.priority, p.arrival, p.id))
                            pick = pref_cands[0]
                            waiting.remove(pick)
                        else:
                            free_cands = [p for p in waiting if p.preferred_server is None]
                            if free_cands:
                                free_cands.sort(key=lambda p: (p.priority, p.arrival, p.id))
                                pick = free_cands[0]
                                waiting.remove(pick)
                            else:
                                continue
                        pick.start_on(sid + 1, t)
                        servers[sid]['p'] = pick
                        servers[sid]['end'] = t + pick.remaining
                        assigned = True

        else:
            t = tc
            # complete any services finishing at time t
            for sid, s in enumerate(servers):
                if s['p'] is not None and s['end'] == t:
                    p = s['p']
                    p.stop_at(t)
                    seg_start = p.segments[-1][1]
                    consumed = int(t) - int(seg_start)
                    p.remaining = max(0, p.remaining - consumed)
                    p.finalize(t)
                    servers[sid] = {'p': None, 'end': None}

            # assign waiting to free servers
            assigned = True
            while assigned:
                assigned = False
                for sid, s in enumerate(servers):
                    if s['p'] is None and waiting:
                        pref_cands = [p for p in waiting if p.preferred_server == sid + 1]
                        if pref_cands:
                            pref_cands.sort(key=lambda p: (p.priority, p.arrival, p.id))
                            pick = pref_cands[0]
                            waiting.remove(pick)
                        else:
                            free_cands = [p for p in waiting if p.preferred_server is None]
                            if free_cands:
                                free_cands.sort(key=lambda p: (p.priority, p.arrival, p.id))
                                pick = free_cands[0]
                                waiting.remove(pick)
                            else:
                                continue
                        pick.start_on(sid + 1, t)
                        servers[sid]['p'] = pick
                        servers[sid]['end'] = t + pick.remaining
                        assigned = True

        # record timeline state after processing this event time `t`
        busy_count = sum(1 for s in servers if s['p'] is not None)
        timeline.append(t)
        queue_lengths.append(len(waiting))
        util_over_time.append(busy_count / servers_count if servers_count > 0 else 0)

    # finalize any unfinished patients (shouldn't happen often, but safe)
    last_completion = 0
    for p in patients:
        if p.end is None:
            if p.first_start is None:
                p.first_start = p.arrival
                p.response = 0
            p.end = p.first_start + p.service
            p.finalize(p.end)
        if p.end > last_completion:
            last_completion = p.end

    # build segments per server for Gantt
    segments = {sid + 1: [] for sid in range(servers_count)}
    for p in patients:
        for seg in p.segments:
            sid, st, en = seg[0], seg[1], seg[2] if seg[2] is not None else seg[1]
            segments[sid].append((p.id, int(st), int(en)))
    for sid in segments:
        segments[sid].sort(key=lambda s: s[1])

    server_busy_raw = {sid: sum(en - st for _, st, en in segments[sid]) for sid in segments}
    total_busy_raw = sum(server_busy_raw.values()) if server_busy_raw else 0

    if servers_count == 1:
        busy = server_busy_raw.get(1, 0)
        total_time = max(1, last_completion)
        util_map = {1: busy / total_time if total_time > 0 else 0.0}
    else:
        if total_busy_raw <= 0:
            util_map = {sid: 1.0 / servers_count for sid in server_busy_raw}
        else:
            util_map = {sid: (busy / total_busy_raw) for sid, busy in server_busy_raw.items()}

    T = max(1, last_completion)

    return {
        'cp': cp, 'cp_lookup': cp_lookup, 'avg': avg_times,
        'inter_arr': inter_arr, 'arrivals': arrivals, 'services': services,
        'priorities': priorities, 'patients': patients, 'segments': segments,
        'busy_raw': server_busy_raw, 'util_map': util_map, 'T': T,
        'timeline': timeline, 'queue': queue_lengths, 'util_time': util_over_time
    }


def simulate_nonpreemptive_fcfs(mean_arrival, mean_service, servers_count=1, dist_type="normal", a=None, b=None):
    cp, cp_lookup, avg_times, inter_arr, arrivals = generate_arrivals_by_cp(mean_arrival)
    n = len(arrivals)
    services = generate_service_times(n, mean_service, dist_type, a=a, b=b)

    patients = [Patient(i + 1, arrivals[i], services[i], priority=None) for i in range(n)]

    servers = [{'p': None, 'end': None} for _ in range(servers_count)]
    waiting = []

    arrival_idx = 0

    # For plotting
    timeline = []
    queue_lengths = []
    util_over_time = []

    def next_arrival_time():
        return patients[arrival_idx].arrival if arrival_idx < n else math.inf

    def next_completion_time():
        times = [s['end'] for s in servers if s['p'] is not None]
        return min(times) if times else math.inf

    while True:
        ta = next_arrival_time()
        tc = next_completion_time()
        if ta == tc == math.inf:
            break

        if ta <= tc:
            t = ta
            arrivals_at_t = []
            while arrival_idx < n and patients[arrival_idx].arrival == t:
                arrivals_at_t.append(patients[arrival_idx])
                arrival_idx += 1

            for newp in arrivals_at_t:
                free_sid = next((sid for sid, s in enumerate(servers) if s['p'] is None), None)
                if free_sid is not None:
                    newp.start_on(free_sid + 1, t)
                    servers[free_sid]['p'] = newp
                    servers[free_sid]['end'] = t + newp.remaining
                else:
                    waiting.append(newp)

            assigned = True
            while assigned:
                assigned = False
                for sid, s in enumerate(servers):
                    if s['p'] is None and waiting:
                        pick = waiting.pop(0)
                        pick.start_on(sid + 1, t)
                        servers[sid]['p'] = pick
                        servers[sid]['end'] = t + pick.remaining
                        assigned = True

        else:
            t = tc
            for sid, s in enumerate(servers):
                if s['p'] is not None and s['end'] == t:
                    p = s['p']
                    p.stop_at(t)
                    seg_start = p.segments[-1][1]
                    consumed = int(t) - int(seg_start)
                    p.remaining = max(0, p.remaining - consumed)
                    p.finalize(t)
                    servers[sid] = {'p': None, 'end': None}

            assigned = True
            while assigned:
                assigned = False
                for sid, s in enumerate(servers):
                    if s['p'] is None and waiting:
                        pick = waiting.pop(0)
                        pick.start_on(sid + 1, t)
                        servers[sid]['p'] = pick
                        servers[sid]['end'] = t + pick.remaining
                        assigned = True

        # record timeline state after processing this event time `t`
        busy_count = sum(1 for s in servers if s['p'] is not None)
        timeline.append(t)
        queue_lengths.append(len(waiting))
        util_over_time.append(busy_count / servers_count if servers_count > 0 else 0)

    last_completion = 0
    for p in patients:
        if p.end is None:
            if p.first_start is None:
                p.first_start = p.arrival
                p.response = 0
            p.end = p.first_start + p.service
            p.finalize(p.end)
        if p.end > last_completion:
            last_completion = p.end

    segments = {sid + 1: [] for sid in range(servers_count)}
    for p in patients:
        for seg in p.segments:
            sid, st, en = seg[0], seg[1], seg[2] if seg[2] is not None else seg[1]
            segments[sid].append((p.id, int(st), int(en)))
    for sid in segments:
        segments[sid].sort(key=lambda s: s[1])

    server_busy_raw = {sid: sum(en - st for _, st, en in segments[sid]) for sid in segments}
    total_busy_raw = sum(server_busy_raw.values()) if server_busy_raw else 0

    if servers_count == 1:
        busy = server_busy_raw.get(1, 0)
        total_time = max(1, last_completion)
        util_map = {1: busy / total_time if total_time > 0 else 0.0}
    else:
        if total_busy_raw <= 0:
            util_map = {sid: 1.0 / servers_count for sid in server_busy_raw}
        else:
            util_map = {sid: (busy / total_busy_raw) for sid, busy in server_busy_raw.items()}

    T = max(1, last_completion)

    return {
        'cp': cp, 'cp_lookup': cp_lookup, 'avg': avg_times,
        'inter_arr': inter_arr, 'arrivals': arrivals, 'services': services,
        'priorities': [None] * n, 'patients': patients, 'segments': segments,
        'busy_raw': server_busy_raw, 'util_map': util_map, 'T': T,
        'timeline': timeline, 'queue': queue_lengths, 'util_time': util_over_time
    }
# --------------------------
# Cinema-themed UI
# --------------------------
class CinemaApp:
    def __init__(self, root):
        # use a dark, cinematic theme
        self.style = tb.Style("darkly")  # darkly is cinematic; user can change
        self.root = self.style.master
        self.root.title("🎬 Cinema Queue Simulator")
        self.root.geometry("1300x860")
        self.root.minsize(1000, 700)

        # top header
        header = ttk.Frame(self.root, padding=(12, 10))
        header.pack(fill=X)
        title = ttk.Label(header, text="🎬 Cinema Queue Simulator", font=("Helvetica", 18, "bold"))
        title.pack(side=LEFT)
        subtitle = ttk.Label(header, text="Simulate ticket counters / concession queues — visualize wait, response & utilization", font=("Helvetica", 10))
        subtitle.pack(side=LEFT, padx=12)

        # top-right quick actions
        actions = ttk.Frame(header)
        actions.pack(side=RIGHT)
        self.theme_var = tk.StringVar(value="darkly")
        ttk.Button(actions, text="Reset", bootstyle=WARNING, command=self.reset_inputs).pack(side=RIGHT, padx=6)
        ttk.Button(actions, text="Export CSV", bootstyle=INFO, command=self.export_csv).pack(side=RIGHT, padx=6)

        # main area: left sidebar + main content
        main = ttk.Frame(self.root)
        main.pack(fill=BOTH, expand=YES, padx=10, pady=(6, 10))

        # ----- sidebar (controls) -----
        sidebar = ttk.Frame(main, width=320, padding=(12, 10))
        sidebar.pack(side=LEFT, fill=Y, padx=(0, 12))
        sidebar.pack_propagate(False)

        # Cinema aesthetic card
        card = ttk.Frame(sidebar, padding=10, bootstyle="secondary")
        card.pack(fill=X, pady=(0, 10))
        ttk.Label(card, text="🎟️ Simulation Controls", font=("Helvetica", 12, "bold")).pack(anchor="w")
        ttk.Label(card, text="Configure arrival, service & model", font=("Helvetica", 9)).pack(anchor="w", pady=(2, 6))

        # controls grid
        form = ttk.Frame(sidebar)
        form.pack(fill=X, pady=(6, 10))

        ttk.Label(form, text="Mean Arrival λ:").grid(row=0, column=0, sticky="w", pady=4)
        self.e_lambda = ttk.Entry(form, width=10); self.e_lambda.insert(0, "1.0"); self.e_lambda.grid(row=0, column=1, sticky="e")

        # Mean Service μ (visible only when dist != uniform)
        self.label_mu = ttk.Label(form, text="Mean Service μ:")
        self.label_mu.grid(row=1, column=0, sticky="w", pady=4)

        self.e_mu = ttk.Entry(form, width=10)
        self.e_mu.insert(0, "1.0")
        self.e_mu.grid(row=1, column=1, sticky="e")

        # Uniform a and b (visible only when dist == uniform)
        self.label_a = ttk.Label(form, text="                     a :")
        self.label_a.grid(row=1, column=0, sticky="w")

        self.e_a = ttk.Entry(form, width=5)
        self.e_a.insert(0, "1")
        self.e_a.grid(row=1, column=1)

        self.label_b = ttk.Label(form, text="b :        ")
        self.label_b.grid(row=1, column=2, sticky="w")

        self.e_b = ttk.Entry(form, width=5)
        self.e_b.insert(0, "5")
        self.e_b.grid(row=1, column=3)

        # Service dist
        ttk.Label(form, text="Service Dist:").grid(row=2, column=0, sticky="w", pady=4)
        self.cb_dist = ttk.Combobox(form, values=["normal", "uniform", "lognormal", "gamma", "exponential"],
                                    width=12, state="readonly")
        self.cb_dist.current(0)
        self.cb_dist.grid(row=2, column=1, sticky="e")
        # bind to change event to show/hide μ vs a/b
        self.cb_dist.bind("<<ComboboxSelected>>", self.on_dist_change)

        ttk.Label(form, text="Priority low:").grid(row=3, column=0, sticky="w", pady=4)
        self.e_plow = ttk.Entry(form, width=6); self.e_plow.insert(0, "1"); self.e_plow.grid(row=3, column=1, sticky="e")

        ttk.Label(form, text="Priority high:").grid(row=4, column=0, sticky="w", pady=4)
        self.e_phigh = ttk.Entry(form, width=6); self.e_phigh.insert(0, "3"); self.e_phigh.grid(row=4, column=1, sticky="e")

        ttk.Label(form, text="Model:").grid(row=5, column=0, sticky="w", pady=6)
        # changed: model is M/G/s or M/M/s
        self.cb_model = ttk.Combobox(form, values=["M/G/s", "M/M/s"], width=12, state="readonly")
        self.cb_model.current(0)
        self.cb_model.grid(row=5, column=1, sticky="e")
        self.cb_model.bind("<<ComboboxSelected>>", self.on_model_change)

        # NEW: Servers input (user types any positive integer)
        ttk.Label(form, text="Servers s:").grid(row=6, column=0, sticky="w", pady=4)
        self.e_servers = ttk.Entry(form, width=6)
        self.e_servers.insert(0, "2")
        self.e_servers.grid(row=6, column=1, sticky="e")

        self.priority_var = tk.BooleanVar(value=True)
        self.chk_priority = ttk.Checkbutton(sidebar, text="Use Preemptive Priority (VIP queue)", variable=self.priority_var)
        self.chk_priority.pack(anchor="w", pady=(8, 6))

        # quick presets for cinema
        ttk.Label(sidebar, text="Presets:", font=("Helvetica", 9, "bold")).pack(anchor="w", pady=(8, 4))
        presets = ttk.Frame(sidebar)
        presets.pack(fill=X)
        ttk.Button(presets, text="Normal Day", bootstyle="success-outline", command=self.preset_normal).pack(side=LEFT, padx=4)
        ttk.Button(presets, text="Peak Show", bootstyle="danger-outline", command=self.preset_peak).pack(side=LEFT, padx=4)
        ttk.Button(presets, text="Matinee", bootstyle="info-outline", command=self.preset_matinee).pack(side=LEFT, padx=4)

        ttk.Label(sidebar, text=" ").pack(fill=X, pady=(6, 6))

        # run button big and cinematic
        ttk.Button(sidebar, text="▶ Run Simulation", bootstyle="primary", command=self.run_sim).pack(fill=X, pady=(6, 4))
        ttk.Button(sidebar, text="⏹ Stop (reset view)", bootstyle="light", command=self.clear_views).pack(fill=X)

        # footer note
        ttk.Label(sidebar, text="Tip: Use VIP queue to model fast-track ticketing.", font=("Helvetica", 8, "italic")).pack(anchor="w", pady=(8, 0))

        # ----- main content (right) -----
        right = ttk.Frame(main)
        right.pack(side=LEFT, fill=BOTH, expand=YES)

        # Notebook
        self.nb = ttk.Notebook(right)
        self.nb.pack(fill=BOTH, expand=YES)

        # Event Table tab (Treeview)
        self.tab_table = ttk.Frame(self.nb)
        self.nb.add(self.tab_table, text="Event Table")
        self.tree_frame = ttk.Frame(self.tab_table)
        self.tree_frame.pack(fill=BOTH, expand=YES, padx=8, pady=8)

        self.tree = ttk.Treeview(self.tree_frame, columns=("no","inter","arrival","service","priority","start","end","turn","wait","resp"), show="headings")
        headings = [("no","S.No"),("inter","InterArr"),("arrival","Arrival"),("service","Service"),("priority","Priority"),
                    ("start","Start"),("end","End"),("turn","Turnaround"),("wait","Wait"),("resp","Resp")]
        for col, head in headings:
            self.tree.heading(col, text=head)
            width = 80 if col != "no" else 60
            self.tree.column(col, width=width, anchor="center")
        self.tree.pack(side=LEFT, fill=BOTH, expand=YES)
        tv_scroll = ttk.Scrollbar(self.tree_frame, orient=VERTICAL, command=self.tree.yview)
        self.tree.configure(yscrollcommand=tv_scroll.set)
        tv_scroll.pack(side=RIGHT, fill=Y)

        # Performance tab (server-level stats)
        self.tab_perf = ttk.Frame(self.nb)
        self.nb.add(self.tab_perf, text="Performance")
        self.perf_frame = ttk.Frame(self.tab_perf)
        self.perf_frame.pack(fill=BOTH, expand=YES, padx=8, pady=8)

        self.tree_perf = ttk.Treeview(self.perf_frame, columns=("server","avgt","avgw","avgr","util"), show="headings")
        perf_heads = [("server","Server"),("avgt","AvgTurn"),("avgw","AvgWait"),("avgr","AvgResp"),("util","Util")]
        for col, head in perf_heads:
            self.tree_perf.heading(col, text=head)
            self.tree_perf.column(col, width=110, anchor="center")
        self.tree_perf.pack(side=LEFT, fill=BOTH, expand=YES)
        pf_scroll = ttk.Scrollbar(self.perf_frame, orient=VERTICAL, command=self.tree_perf.yview)
        self.tree_perf.configure(yscrollcommand=pf_scroll.set)
        pf_scroll.pack(side=RIGHT, fill=Y)

        # Graphical View tab (Gantt + charts area)
        self.tab_graph = ttk.Frame(self.nb)
        self.nb.add(self.tab_graph, text="Graphical View")
        self.gantt_frame = ttk.Frame(self.tab_graph)
        self.gantt_frame.pack(fill=BOTH, expand=YES, padx=8, pady=8)

        # Keep last result for export
        self.last_result = None

        # initial adjust visibility (hide a/b since default dist is normal)
        self.on_dist_change()

    # ---------- helper UI actions ----------
    def reset_inputs(self):
        self.e_lambda.delete(0, END); self.e_lambda.insert(0, "1.0")
        self.e_mu.delete(0, END); self.e_mu.insert(0, "1.0")
        self.e_a.delete(0, END); self.e_a.insert(0, "1")
        self.e_b.delete(0, END); self.e_b.insert(0, "5")
        self.cb_dist.set("normal")
        self.cb_model.set("M/G/s")
        self.e_servers.delete(0, END); self.e_servers.insert(0, "2")
        self.priority_var.set(True)
        self.clear_views()
        self.on_dist_change()

    def clear_views(self):
        # clear trees and charts
        for i in self.tree.get_children():
            self.tree.delete(i)
        for i in self.tree_perf.get_children():
            self.tree_perf.delete(i)
        for w in self.gantt_frame.winfo_children():
            w.destroy()
    def export_csv(self):
        # simple CSV export of event table (asks user for filename)
        if not self.last_result:
            messagebox.showinfo("No data", "Run a simulation first before exporting.")
            return
        import csv
        from tkinter.filedialog import asksaveasfilename
        fname = asksaveasfilename(defaultextension=".csv", filetypes=[("CSV files","*.csv")], title="Save Event Table")
        if not fname:
            return
        try:
            with open(fname, "w", newline="") as f:
                writer = csv.writer(f)
                if self.priority_var.get():
                    hdr = ["S.No","InterArr","Arrival","Service","Priority","Start","End","Turnaround","Wait","Resp"]
                else:
                    hdr = ["S.No","InterArr","Arrival","Service","Start","End","Turnaround","Wait","Resp"]
                writer.writerow(hdr)
                for i, p in enumerate(self.last_result['patients']):
                    if self.priority_var.get():
                        writer.writerow([i+1, self.last_result['inter_arr'][i], self.last_result['arrivals'][i],
                                         self.last_result['services'][i], p.priority if p.priority is not None else "",
                                         p.first_start if p.first_start is not None else 0,
                                         p.end if p.end is not None else 0,
                                         p.turnaround if p.turnaround is not None else 0,
                                         p.wait if p.wait is not None else 0,
                                         p.response if p.response is not None else 0])
                    else:
                        writer.writerow([i+1, self.last_result['inter_arr'][i], self.last_result['arrivals'][i],
                                         self.last_result['services'][i],
                                         p.first_start if p.first_start is not None else 0,
                                         p.end if p.end is not None else 0,
                                         p.turnaround if p.turnaround is not None else 0,
                                         p.wait if p.wait is not None else 0,
                                         p.response if p.response is not None else 0])
            messagebox.showinfo("Saved", f"Event table exported to:\n{fname}")
        except Exception as e:
            messagebox.showerror("Error", f"Failed to save file: {e}")

    # ---------- presets ----------
    def preset_normal(self):
        self.e_lambda.delete(0, END); self.e_lambda.insert(0, "0.8")
        self.e_mu.delete(0, END); self.e_mu.insert(0, "1.2")
        self.cb_model.set("M/G/s")
        self.e_servers.delete(0, END); self.e_servers.insert(0, "2")
        self.cb_dist.set("normal")
        self.priority_var.set(True)
        self.on_dist_change()

    def preset_peak(self):
        self.e_lambda.delete(0, END); self.e_lambda.insert(0, "2.5")
        self.e_mu.delete(0, END); self.e_mu.insert(0, "1.0")
        self.cb_model.set("M/G/s")
        self.e_servers.delete(0, END); self.e_servers.insert(0, "4")
        self.cb_dist.set("gamma")
        self.priority_var.set(True)
        self.on_dist_change()

    def preset_matinee(self):
        self.e_lambda.delete(0, END); self.e_lambda.insert(0, "0.5")
        # for uniform preset set a & b and set dist to uniform
        self.e_a.delete(0, END); self.e_a.insert(0, "1")
        self.e_b.delete(0, END); self.e_b.insert(0, "3")
        self.cb_model.set("M/G/s")
        self.e_servers.delete(0, END); self.e_servers.insert(0, "1")
        self.cb_dist.set("uniform")
        self.priority_var.set(False)
        self.on_dist_change()

    # show/hide fields depending on distribution selection
    def on_dist_change(self, event=None):
        dist = self.cb_dist.get()

        if dist == "uniform":
            # hide μ
            self.label_mu.grid_remove()
            self.e_mu.grid_remove()

            # show a & b
            self.label_a.grid()
            self.e_a.grid()
            self.label_b.grid()
            self.e_b.grid()

        else:
            # show μ
            self.label_mu.grid()
            self.e_mu.grid()

            # hide a & b
            self.label_a.grid_remove()
            self.e_a.grid_remove()
            self.label_b.grid_remove()
            self.e_b.grid_remove()

        # If model forces exponential service (M/M/...)
        model = self.cb_model.get()
        if model.startswith("M/M"):
            self.cb_dist.set("exponential")
            # show μ again
            self.label_mu.grid()
            self.e_mu.grid()
            # hide a/b
            self.label_a.grid_remove()
            self.e_a.grid_remove()
            self.label_b.grid_remove()
            self.e_b.grid_remove()


    def on_model_change(self, event=None):
        model = self.cb_model.get()
        if model.startswith("M/M"):
            # force exponential
            self.cb_dist.set("exponential")
            self.on_dist_change()
        else:
            # leave existing distribution as-is
            self.on_dist_change()

    # ---------- main run ----------
    def run_sim(self):
        try:
            lam = float(self.e_lambda.get())
            # determine distribution type and read fields appropriately
            dist_type = self.cb_dist.get()

            if dist_type == "uniform":
                # read a and b
                try:
                    a = float(self.e_a.get())
                    b = float(self.e_b.get())
                except Exception:
                    messagebox.showerror("Invalid Input", "Enter valid numeric values for a and b.")
                    return
                if b <= a:
                    messagebox.showwarning("Invalid Input", "Value b must be greater than a for uniform distribution.")
                    return
                mu = None
            else:
                # read mean service mu
                try:
                    mu = float(self.e_mu.get())
                except Exception:
                    messagebox.showerror("Invalid Input", "Enter valid numeric value for mean service μ.")
                    return
                if mu <= 0:
                    messagebox.showwarning("Invalid Input", "Mean service time must be positive.")
                    return
                a = None
                b = None

            pl = int(self.e_plow.get()); ph = int(self.e_phigh.get())
            if pl > ph:
                raise ValueError("priority low > high")
            if lam <= 0:
                messagebox.showwarning("Invalid Input", "Mean arrival must be positive.")
                return
        except Exception as e:
            messagebox.showerror("Invalid input", f"Enter valid numeric values. {e}")
            return

        # NEW: read servers count from the entry (user can type any positive integer)
        try:
            servers = int(self.e_servers.get())
            if servers <= 0:
                raise ValueError("servers must be positive")
        except Exception as e:
            messagebox.showerror("Invalid Input", "Enter valid number of servers (positive integer).")
            return

        use_priority = bool(self.priority_var.get())

        # If user picked M/M/s, force exponential service distribution
        model = self.cb_model.get()
        if model.startswith("M/M"):
            dist_type = "exponential"
            # ensure μ is used (exponential requires mu)
            if mu is None:
                # try to fall back: if a/b present, estimate mean as average
                if a is not None and b is not None:
                    mu = (a + b) / 2.0
                else:
                    mu = 1.0

        if use_priority:
            # preemptive priority simulation handles priorities
            res = simulate_preemptive_v5(lam, mu, servers_count=servers, pr_range=(pl, ph), dist_type=dist_type, a=a, b=b)
        else:
            res = simulate_nonpreemptive_fcfs(lam, mu, servers_count=servers, dist_type=dist_type, a=a, b=b)

        # store last result
        self.last_result = res

        # populate event table treeview
        self.populate_event_table(res, use_priority)

        # populate performance table
        self.populate_performance(res)

        # draw charts / gantt
        self.draw_gantt_and_charts(res['segments'], res['patients'], use_priority, model,
                                   timeline=res.get('timeline', []), queue=res.get('queue', []), util_time=res.get('util_time', []))

    def populate_event_table(self, res, use_priority):
        # clear
        for i in self.tree.get_children():
            self.tree.delete(i)
        # insert rows
        if use_priority:
            for i, p in enumerate(res['patients']):
                vals = (i+1, res['inter_arr'][i], res['arrivals'][i], res['services'][i],
                        p.priority if p.priority is not None else "", p.first_start if p.first_start is not None else 0,
                        p.end if p.end is not None else 0, p.turnaround if p.turnaround is not None else 0,
                        p.wait if p.wait is not None else 0, p.response if p.response is not None else 0)
                self.tree.insert("", "end", values=vals)
        else:
            for i, p in enumerate(res['patients']):
                vals = (i+1, res['inter_arr'][i], res['arrivals'][i], res['services'][i],
                        "", p.first_start if p.first_start is not None else 0,
                        p.end if p.end is not None else 0, p.turnaround if p.turnaround is not None else 0,
                        p.wait if p.wait is not None else 0, p.response if p.response is not None else 0)
                self.tree.insert("", "end", values=vals)

    def populate_performance(self, res):
        for i in self.tree_perf.get_children():
            self.tree_perf.delete(i)
        util_map = res['util_map']
        formatted_utils = {sid: float(f"{u:.3f}") for sid, u in util_map.items()}

        if len(formatted_utils) == 2:
            total_rounded = sum(formatted_utils.values())
            diff = round(1.0 - total_rounded, 3)
            if abs(diff) >= 0.001:
                largest_sid = max(util_map.items(), key=lambda kv: kv[1])[0]
                formatted_utils[largest_sid] = round(formatted_utils[largest_sid] + diff, 3)

        for sid, segs in sorted(res['segments'].items()):
            pids = [pid for pid, _, _ in segs]
            pats = [p for p in res['patients'] if p.id in pids]
            if not pats:
                continue
            avgt = mean([p.turnaround for p in pats])
            avgw = mean([p.wait for p in pats])
            avgr = mean([p.response for p in pats])
            util_display = formatted_utils.get(sid, 0.0)
            self.tree_perf.insert("", "end", values=(sid, f"{avgt:.1f}", f"{avgw:.1f}", f"{avgr:.1f}", f"{util_display:.3f}"))


    # draw_gantt_and_charts adapted to pack into gantt_frame (re-used mostly)
    def draw_gantt_and_charts(self, segments, patients, use_priority, model, timeline=None, queue=None, util_time=None):
        for w in self.gantt_frame.winfo_children():
            w.destroy()

        fig = plt.figure(figsize=(10, 7))
        gs = fig.add_gridspec(nrows=3, ncols=1, height_ratios=[len(segments) * 0.6 + 1.5, 1.5, 1.5])

        ax_gantt = fig.add_subplot(gs[0, 0])
        ax_q = fig.add_subplot(gs[1, 0], sharex=ax_gantt)
        ax_u = fig.add_subplot(gs[2, 0], sharex=ax_gantt)

        # priority colors for preemptive mode (unchanged)
        pri_colors = {1: "#ff4d4d", 2: "#ffd24d", 3: "#4dff88"}
        # For non-preemptive (user requested): 3-color cycle red, yellow, green
        cycle_colors = {0: "#ff4d4d", 1: "#ffd24d", 2: "#4dff88"}

        fallback_colors = plt.cm.get_cmap("tab20")

        bar_rects = []
        y = 0
        for sid in sorted(segments.keys()):
            for pid, st, en in segments[sid]:
                p = next((pp for pp in patients if pp.id == pid), None)
                priority = p.priority if p is not None else None

                # choose color:
                if use_priority and priority in pri_colors:
                    color = pri_colors[priority]
                else:
                    # non-preemptive: cycle 3 colors by pid (1->red,2->yellow,3->green,4->red,...)
                    try:
                        color = cycle_colors[(pid - 1) % 3]
                    except Exception:
                        color = fallback_colors(pid % 20)

                width = max(0.001, en - st)
                rects = ax_gantt.barh(y, width, left=st, height=0.6, color=color, edgecolor='k')
                r = rects[0]
                bar_rects.append((r, pid, p.service if p is not None else None))
            ax_gantt.text(-1, y, f"Counter {sid}", va='center', ha='right', fontsize=9)
            y += 1

        ax_gantt.set_ylabel('Service Counters')
        ax_gantt.set_title(f"Gantt Chart ({model}) — Cinematic View")
        ax_gantt.grid(axis='x', linestyle='--', alpha=0.5)

        if use_priority:
            legend_handles = []
            labels = []
            for pri, col in pri_colors.items():
                h = plt.Rectangle((0, 0), 1, 1, color=col, edgecolor='k')
                legend_handles.append(h)
                labels.append(f"Priority {pri}")
            ax_gantt.legend(legend_handles, labels, loc='center left', bbox_to_anchor=(1.02, 0.5), borderaxespad=0.)
        else:
            # show small legend for the 3-color cycle so users know mapping
            legend_handles = []
            labels = []
            legend_handles.append(plt.Rectangle((0, 0), 1, 1, color=cycle_colors[0], edgecolor='k'))
            labels.append("Customer 1 (also 4,7,...)")
            legend_handles.append(plt.Rectangle((0, 0), 1, 1, color=cycle_colors[1], edgecolor='k'))
            labels.append("Customer 2 (also 5,8,...)")
            legend_handles.append(plt.Rectangle((0, 0), 1, 1, color=cycle_colors[2], edgecolor='k'))
            labels.append("Customer 3 (also 6,9,...)")
            ax_gantt.legend(legend_handles, labels, loc='center left', bbox_to_anchor=(1.02, 0.5), borderaxespad=0.)
        canvas = FigureCanvasTkAgg(fig, master=self.gantt_frame)
        annot = ax_gantt.annotate("", xy=(0, 0), xytext=(15, 15), textcoords="offset points",
                                  bbox=dict(boxstyle="round", fc="w"),
                                  arrowprops=dict(arrowstyle="->"))
        annot.set_visible(False)

        def update_annot(event, rect, pid, service):
            start = rect.get_x()
            width = rect.get_width()
            end_time = start + width
            annot.xy = (event.xdata if event.xdata is not None else start, event.ydata if event.ydata is not None else rect.get_y())
            txt = f"Customer: C{pid}\nService Time: {service}\nEnd Time: {int(round(end_time))}"
            annot.set_text(txt)
            annot.get_bbox_patch().set_alpha(0.95)

        def hover(event):
            vis = annot.get_visible()
            if event.inaxes == ax_gantt:
                found = False
                for r, pid, service in bar_rects:
                    contains, _ = r.contains(event)
                    if contains:
                        update_annot(event, r, pid, service)
                        annot.set_visible(True)
                        canvas.draw_idle()
                        found = True
                        break
                if not found and vis:
                    annot.set_visible(False)
                    canvas.draw_idle()

        canvas.mpl_connect("motion_notify_event", hover)

        # Queue Length vs Time
        if timeline and queue:
            ax_q.plot(timeline, queue)
            ax_q.set_ylabel('Queue Length')
            ax_q.grid(True, linestyle='--', alpha=0.5)
        else:
            ax_q.text(0.5, 0.5, 'No data', ha='center', va='center')

        # Server Utilization vs Time
        if timeline and util_time:
            ax_u.plot(timeline, util_time)
            ax_u.set_ylabel('Utilization (fraction busy)')
            ax_u.set_xlabel('Time')
            ax_u.grid(True, linestyle='--', alpha=0.5)
        else:
            ax_u.text(0.5, 0.5, 'No data', ha='center', va='center')

        plt.tight_layout()
        canvas.draw()
        widget = canvas.get_tk_widget()
        widget.pack(fill=BOTH, expand=YES)


# --------------------------
# Run
# --------------------------
if __name__ == "__main__":
    root = tb.Window(themename="darkly")
    app = CinemaApp(root)
    root.mainloop()
