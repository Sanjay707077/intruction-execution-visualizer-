import customtkinter as ctk
import tkinter as tk
from tkinter import filedialog, messagebox
from PIL import Image, ImageTk
import re, time, math, csv, json, threading, os
from dataclasses import dataclass, field
from typing import List, Dict, Optional, Tuple

ctk.set_appearance_mode("dark")
ctk.set_default_color_theme("blue")
APP_TITLE = "INSTRUCTION EXECUTION VISUALIZER"
WINDOW_MIN_W = 1200
WINDOW_MIN_H = 750
STAGES = ["Fetch", "Decode", "Execute", "Memory", "WriteBack"]
NUM_REGS = 8
MEM_SIZE = 64
TOKEN_W = 160
TOKEN_H = 36
ROW_H = 40
STAGE_COL_W = 160
INSTR_COL_W = 280
BG = "#0b1220"
CARD_BG = "#0f172a"
ACTIVE_COLOR = "#06b6d4"
TOKEN_COLOR = "#06d6a0"
BUBBLE_COLOR = "#334155"
TEXT_COLOR = "#e6eef8"
STAGE_BG = "#071428"
STAGE_LINE = "#1e3a8a"

def lerp(a, b, t):
    return a + (b - a) * t
def ease_out_quad(t):
    return 1 - (1 - t) * (1 - t)

@dataclass
class Instruction:
    raw: str
    op: str = ""
    dst: Optional[str] = None
    src1: Optional[str] = None
    src2: Optional[str] = None
    imm: Optional[int] = None
    result: str = ""
    def __post_init__(self):
        self.raw = self.raw.strip()
        parts = re.split(r"[,\s]+", self.raw)
        if not parts or not parts[0]:
            return
        self.op = parts[0].upper()
        try:
            if self.op == "LOAD":
                self.dst = parts[1].upper()
                imm_part = parts[2]
                if imm_part.startswith("[") and imm_part.endswith("]"):
                    addr = int(imm_part.strip("[]"))
                    self.imm = addr
                else:
                    self.imm = int(imm_part)
            elif self.op == "STORE":
                self.src1 = parts[1].upper()
                self.imm = int(parts[2])
            elif self.op in ("ADD", "SUB", "MUL", "DIV"):
                self.dst = parts[1].upper()
                self.src1 = parts[2].upper()
                raw3 = parts[3]
                if raw3.upper().startswith("R"):
                    self.src2 = raw3.upper()
                else:
                    self.imm = int(raw3)
            elif self.op == "MOV":
                self.dst = parts[1].upper()
                raw2 = parts[2]
                if raw2.upper().startswith("R"):
                    self.src1 = raw2.upper()
                else:
                    self.imm = int(raw2)
            elif self.op == "BEQ":
                self.src1 = parts[1].upper()
                self.src2 = parts[2].upper()
                if len(parts) > 3:
                    self.imm = int(parts[3])
                else:
                    self.imm = 0
            valid_regs = {f"R{i}" for i in range(1, NUM_REGS + 1)}
            if self.dst and self.dst not in valid_regs:
                self.dst = None
            if self.src1 and self.src1.startswith('R') and self.src1 not in valid_regs:
                self.src1 = None
            if self.src2 and self.src2.startswith('R') and self.src2 not in valid_regs:
                self.src2 = None
        except (IndexError, ValueError):
            pass

@dataclass
class Token:
    instr: Instruction
    stage_idx: int = -1
    bubble: bool = False
    id: int = 0
    x: float = 0.0
    y: float = 0.0
    start_x: float = 0.0
    start_y: float = 0.0
    target_x: float = 0.0
    target_y: float = 0.0
    anim_start_time: float = 0.0
    anim_duration: float = 0.25
    def is_completed(self):
        return self.stage_idx >= len(STAGES)

class PipelineEngine:
    def __init__(self, registers: Dict[str, int], memory: List[int]):
        self.registers = registers
        self.memory = memory
        self.program: List[Instruction] = []
        self.tokens: List[Token] = []
        self.pc = 0
        self.cycle = 0
        self.stalls = 0
        self.forwards = 0
        self.completed_instrs = 0
        self.log: List[Dict] = []
        self.next_token_id = 1
        self.stalling_token_id: Optional[int] = None
    def load_program(self, lines: List[str]):
        self.program = [Instruction(line) for line in lines if line.strip() and not line.strip().startswith('#')]
        self.reset_state(keep_regs=False)
    def reset_state(self, keep_regs=False):
        self.tokens = []
        self.pc = 0
        self.cycle = 0
        self.stalls = 0
        self.forwards = 0
        self.completed_instrs = 0
        self.log = []
        self.next_token_id = 1
        self.stalling_token_id = None
        if not keep_regs:
            for k in self.registers:
                self.registers[k] = 0
            for i in range(len(self.memory)):
                self.memory[i] = 0
    def can_fetch(self):
        return self.pc < len(self.program)
    def detect_raw_hazard(self, token: Token) -> Tuple[bool, Optional[Token]]:
        instr = token.instr
        sources = {s for s in (instr.src1, instr.src2) if s and s.startswith("R")}
        if not sources:
            return False, None
        earlier_tokens = [t for t in self.tokens if t.id < token.id and not t.bubble]
        for other in earlier_tokens:
            if other.instr.dst and other.instr.dst in sources:
                if other.stage_idx < 3:
                    return True, other
        return False, None
    def detect_forwarding_possibility(self, token: Token, hazard_token: Token) -> int:
        forwarded = 0
        instr = token.instr
        sources = {s for s in (instr.src1, instr.src2) if s and s.startswith("R")}
        if not hazard_token:
            return 0
        if hazard_token.instr.dst in sources:
            if hazard_token.stage_idx in (2, 3):
                if instr.src1 == hazard_token.instr.dst:
                    forwarded += 1
                if instr.src2 == hazard_token.instr.dst:
                    forwarded += 1
        return forwarded
    def step(self, use_forwarding=False):
        self.cycle += 1
        cycle_events = {"cycle": self.cycle, "actions": []}
        for t in list(self.tokens):
            if t.stage_idx == len(STAGES) - 1 and not t.bubble:
                self._apply_writeback(t.instr)
                cycle_events["actions"].append({"type": "writeback", "id": t.id, "instr": t.instr.raw, "result": t.instr.result})
        stalled = False
        self.stalling_token_id = None
        decode_token = next((t for t in self.tokens if t.stage_idx == 1 and not t.bubble), None)
        hazard_token = None
        if decode_token:
            hazard, hazard_token = self.detect_raw_hazard(decode_token)
            if hazard:
                forwarded_sources = self.detect_forwarding_possibility(decode_token, hazard_token) if use_forwarding else 0
                if forwarded_sources > 0:
                    self.forwards += forwarded_sources
                    cycle_events["actions"].append({"type": "forwarded", "id": decode_token.id, "dep_id": hazard_token.id, "sources": forwarded_sources})
                else:
                    stalled = True
                    self.stalls += 1
                    self.stalling_token_id = decode_token.id
                    cycle_events["actions"].append({"type": "stalled", "id": decode_token.id, "dep_id": hazard_token.id})
        for t in sorted(self.tokens, key=lambda x: -x.stage_idx):
            if t.bubble:
                t.stage_idx += 1
                continue
            if t.stage_idx >= len(STAGES):
                continue
            if stalled and t.stage_idx in (0, 1):
                continue
            t.stage_idx += 1
        completed_tokens = [t for t in self.tokens if t.is_completed()]
        for t in completed_tokens:
            self.tokens.remove(t)
            self.completed_instrs += 1
            cycle_events["actions"].append({"type": "completed", "id": t.id, "instr": t.instr.raw})
        if self.can_fetch():
            if not stalled:
                instr = self.program[self.pc]
                token = Token(instr=instr, stage_idx=0, id=self.next_token_id)
                self.next_token_id += 1
                self.tokens.append(token)
                self.pc += 1
                cycle_events["actions"].append({"type": "fetched", "id": token.id, "instr": instr.raw})
            else:
                nop_instr = Instruction("NOP")
                bubble_token = Token(instr=nop_instr, stage_idx=0, bubble=True, id=self.next_token_id)
                self.next_token_id += 1
                self.tokens.append(bubble_token)
                cycle_events["actions"].append({"type": "bubble", "id": bubble_token.id})
        self.log.append(cycle_events)
        return cycle_events
    def _apply_writeback(self, instr: Instruction):
        op = (instr.op or "").upper()
        result_str = "No change"
        try:
            if op in ("ADD", "SUB", "MUL", "DIV"):
                v1 = self.registers.get(instr.src1, 0) if instr.src1 else 0
                if instr.src2:
                    v2 = self.registers.get(instr.src2, 0)
                else:
                    v2 = instr.imm if instr.imm is not None else 0
                if op == "ADD":
                    res = v1 + v2
                elif op == "SUB":
                    res = v1 - v2
                elif op == "MUL":
                    res = v1 * v2
                elif op == "DIV":
                    res = v1 // v2 if v2 != 0 else 0
                else:
                    res = 0
                if instr.dst:
                    self.registers[instr.dst] = res
                    result_str = f"{instr.dst} <= {res}"
            elif op == "MOV":
                val = self.registers.get(instr.src1, 0) if instr.src1 else instr.imm if instr.imm is not None else 0
                if instr.dst:
                    self.registers[instr.dst] = val
                    result_str = f"{instr.dst} <= {val}"
            elif op == "LOAD":
                if instr.dst:
                    if instr.raw.find("[") != -1 and instr.raw.find("]") != -1:
                        try:
                            addr = instr.imm if instr.imm is not None else 0
                            addr = int(addr) % len(self.memory)
                            val = self.memory[addr]
                            self.registers[instr.dst] = val
                            result_str = f"{instr.dst} <= M[{addr}] ({val})"
                        except Exception:
                            self.registers[instr.dst] = 0
                            result_str = f"{instr.dst} <= 0 (mem-load error)"
                    else:
                        val = instr.imm if instr.imm is not None else 0
                        self.registers[instr.dst] = val
                        result_str = f"{instr.dst} <= {val}"
            elif op == "STORE":
                if instr.src1:
                    addr = instr.imm if instr.imm is not None else 0
                    addr = int(addr) % len(self.memory)
                    val = self.registers.get(instr.src1, 0)
                    self.memory[addr] = val
                    result_str = f"M[{addr}] <= {val}"
            elif op == "BEQ":
                result_str = "Branch (simple) - resolved in decode"
            elif op == "NOP":
                result_str = "NOP"
            else:
                result_str = "Unknown op"
        except Exception as e:
            result_str = f"Error: {e}"
        instr.result = result_str

class PipelineCanvas(tk.Canvas):
    def __init__(self, master, engine: PipelineEngine, app, **kwargs):
        super().__init__(master, **kwargs)
        self.engine = engine
        self.app = app
        self.bind("<Configure>", lambda e: self.draw())
        self.active_token_id: Optional[int] = None
        self.bind("<Motion>", self._on_motion)
        self.bind("<Leave>", self._on_leave)
        self.token_positions: Dict[int, Tuple[float, float]] = {}
    def _on_motion(self, event):
        found = False
        for token in self.engine.tokens:
            x, y = token.x, token.y
            if x <= event.x <= x + TOKEN_W and y <= event.y <= y + TOKEN_H:
                if self.active_token_id != token.id:
                    self.active_token_id = token.id
                    self.app.update_inspector(token)
                    self.draw()
                found = True
                break
        if not found:
            self._on_leave(event)
    def _on_leave(self, event):
        if self.active_token_id is not None:
            self.active_token_id = None
            self.app.update_inspector(None)
            self.draw()
    def draw(self):
        self.delete("all")
        w = max(self.winfo_width(), INSTR_COL_W + len(STAGES) * (STAGE_COL_W + 20) + 120)
        h = max(self.winfo_height(), 480)
        left = 20
        top = 30
        prog_x = left
        prog_w = INSTR_COL_W - 20
        self.create_rectangle(prog_x - 10, 10, prog_x + prog_w, h - 10, fill="#121e33", outline=STAGE_LINE, width=2)
        self.create_text(prog_x + prog_w / 2, 25, text="Program (PC)", fill=ACTIVE_COLOR, font=("Segoe UI", 12, "bold"))
        for i, instr in enumerate(self.engine.program):
            y = 50 + i * ROW_H + ROW_H/2
            txt = f"{i:02}: {instr.raw}"
            self.create_text(prog_x + 20, y, text=txt, fill=TEXT_COLOR, font=("Consolas", 10), anchor="w")
        pc_marker_y = 50 + self.engine.pc * ROW_H + ROW_H/2
        if 0 <= self.engine.pc < len(self.engine.program):
            self.create_text(prog_x + 6, pc_marker_y, text="➤", fill="#fde047", font=("Consolas", 12), anchor="w")
        for idx, st in enumerate(STAGES):
            sx = prog_x + prog_w + 30 + idx * (STAGE_COL_W + 10)
            self.create_rectangle(sx, 10, sx + STAGE_COL_W, h - 10, fill=STAGE_BG, outline=STAGE_LINE)
            self.create_text(sx + STAGE_COL_W / 2, 25, text=st, fill="#9fe6ff", font=("Segoe UI", 12, "bold"))
        for i, token in enumerate(self.engine.tokens):
            row_y = 70 + i * (TOKEN_H + 10)
            stage_idx = token.stage_idx if not token.bubble else token.stage_idx
            stage_idx = max(0, stage_idx)
            sx = prog_x + prog_w + 30 + stage_idx * (STAGE_COL_W + 10)
            tx = sx + (STAGE_COL_W - TOKEN_W) / 2
            ty = row_y
            if token.id not in self.token_positions:
                start_x = prog_x + 12
                start_y = ty
                token.x = start_x
                token.y = start_y
                self.token_positions[token.id] = (start_x, start_y)
            cur_x, cur_y = self.token_positions[token.id]
            nx = lerp(cur_x, tx, 0.35)
            ny = lerp(cur_y, ty, 0.35)
            token.x, token.y = nx, ny
            self.token_positions[token.id] = (nx, ny)
            outline_color = "#fb923c" if token.id == self.active_token_id else "#053f3f"
            if token.id == self.engine.stalling_token_id:
                outline_color = "#f87171"
            fill_color = BUBBLE_COLOR if token.bubble else TOKEN_COLOR
            op_block_fill = "#374151" if token.bubble else "#054e57"
            self.create_rectangle(nx+3, ny+3, nx + TOKEN_W + 3, ny + TOKEN_H + 3, fill="#000000", outline="")
            self.create_rectangle(nx, ny, nx + TOKEN_W, ny + TOKEN_H, fill=fill_color, outline=outline_color, width=2)
            self.create_rectangle(nx, ny, nx + 46, ny + TOKEN_H, fill=op_block_fill, outline="")
            self.create_text(nx + 23, ny + TOKEN_H / 2, text=token.instr.op or "NOP", fill="white", font=("Segoe UI", 10, "bold"))
            self.create_text(nx + 52, ny + TOKEN_H / 2, text=token.instr.raw, fill=TEXT_COLOR, font=("Consolas", 9), anchor="w")
        self.create_text(w - 160, 20, text=f"Cycle: {self.engine.cycle}", fill="#fef3c7", font=("Segoe UI", 14, "bold"))
        self.create_text(w - 160, 40, text=f"Completed: {self.engine.completed_instrs}", fill="#c7f9cc", font=("Segoe UI", 11))

class PipelineApp(ctk.CTk):
    def __init__(self):
        super().__init__()
        self.title(APP_TITLE)
        self.minsize(WINDOW_MIN_W, WINDOW_MIN_H)
        self.geometry(f"{WINDOW_MIN_W}x{WINDOW_MIN_H}")
        self.registers = {f"R{i}": 0 for i in range(1, NUM_REGS + 1)}
        self.memory = [0] * MEM_SIZE
        self.engine = PipelineEngine(self.registers, self.memory)
        self.playing = False
        self.use_forwarding = ctk.BooleanVar(value=True)
        self.speed = ctk.DoubleVar(value=1.0)
        self.speed.trace_add("write", self._on_speed_change)
        self._anim_running = False
        self._build_ui()
        self._layout_ui()
        self._bind_shortcuts()
        self.program_txt.insert("1.0", "LOAD R1, 10\nLOAD R2, 20\nADD R3, R1, R2\nADD R4, R3, 5\nSTORE R4, 12\nSUB R5, R4, R1")
        self._on_load_program(initial=True)
        self.after(30, self._animation_tick)
    def _build_ui(self):
        self.header = ctk.CTkFrame(self, height=70, corner_radius=0, fg_color=CARD_BG)
        self.logo_lbl = ctk.CTkLabel(self.header, text=APP_TITLE, font=ctk.CTkFont(size=20, weight="bold"))
        self.main_left_frame = ctk.CTkFrame(self, fg_color="transparent")
        self.control_frame = ctk.CTkFrame(self.main_left_frame, fg_color=CARD_BG)
        self.vis_frame = ctk.CTkFrame(self.main_left_frame, fg_color=CARD_BG)
        self.program_txt = tk.Text(self.control_frame, height=10, font=("Consolas", 11), bg="#071428", fg=TEXT_COLOR, insertbackground="white", relief="flat")
        self.load_btn = ctk.CTkButton(self.control_frame, text="Load Program", command=self._on_load_program)
        self.run_btn = ctk.CTkButton(self.control_frame, text="▶ Play", command=self._toggle_play, fg_color="#10b981", hover_color="#059669")
        self.step_btn = ctk.CTkButton(self.control_frame, text="Step ➡", command=self._on_step, fg_color="#3b82f6", hover_color="#2563eb")
        self.reset_btn = ctk.CTkButton(self.control_frame, text="Reset", command=self._on_reset, fg_color="#ef4444", hover_color="#dc2626")
        self.forward_chk = ctk.CTkCheckBox(self.control_frame, text="Data Forwarding", variable=self.use_forwarding)
        self.speed_slider = ctk.CTkSlider(self.control_frame, from_=0.5, to=5.0, variable=self.speed)
        self.speed_lbl = ctk.CTkLabel(self.control_frame, text=f"Speed: {self.speed.get():.1f}x", width=80)
        self.export_btn = ctk.CTkButton(self.control_frame, text="Export Log", command=self._on_export_log)
        self.canvas = PipelineCanvas(self.vis_frame, self.engine, self, bg=BG, highlightthickness=0)
        self.right_tabs = ctk.CTkTabview(self, width=320, fg_color=CARD_BG)
        for tab_name in ["Registers", "Memory", "Stats", "Log"]:
            self.right_tabs.add(tab_name)
        self.reg_list = tk.Listbox(self.right_tabs.tab("Registers"), font=("Consolas", 11), bg="#071428", fg=TEXT_COLOR, bd=0)
        self.mem_list = tk.Listbox(self.right_tabs.tab("Memory"), font=("Consolas", 11), bg="#071428", fg=TEXT_COLOR, bd=0)
        self.stats_text = tk.Text(self.right_tabs.tab("Stats"), font=("Consolas", 12), bg="#071428", fg=TEXT_COLOR, bd=0, state=tk.DISABLED)
        self.log_txt = tk.Text(self.right_tabs.tab("Log"), font=("Consolas", 10), bg="#071428", fg=TEXT_COLOR, bd=0, wrap="word")
        self.inspector = ctk.CTkFrame(self, corner_radius=12, fg_color=CARD_BG)
        self.inspector_lbl = ctk.CTkLabel(self.inspector, text="Instruction Inspector", font=ctk.CTkFont(size=14, weight="bold"))
        self.inspector_text = tk.Text(self.inspector, height=4, font=("Consolas", 11), bg="#071428", fg=TEXT_COLOR, relief="flat", wrap="word", state=tk.DISABLED)
    def _layout_ui(self):
        self.grid_columnconfigure(0, weight=1)
        self.grid_columnconfigure(1, weight=0)
        self.grid_rowconfigure(0, weight=0)
        self.grid_rowconfigure(1, weight=1)
        self.grid_rowconfigure(2, weight=0)
        self.header.grid(row=0, column=0, columnspan=2, sticky="nsew", padx=8, pady=(8,4))
        self.logo_lbl.pack(side="left", padx=20, pady=10)
        self.main_left_frame.grid(row=1, column=0, sticky="nsew", padx=(8,4), pady=4)
        self.main_left_frame.grid_rowconfigure(0, weight=0)
        self.main_left_frame.grid_rowconfigure(1, weight=1)
        self.main_left_frame.grid_columnconfigure(0, weight=1)
        self.control_frame.grid(row=0, column=0, sticky="new", pady=(0,4))
        self.vis_frame.grid(row=1, column=0, sticky="nsew")
        self.control_frame.grid_columnconfigure((0,1,2,3), weight=1)
        self.program_txt.grid(row=0, column=0, columnspan=4, sticky="nsew", padx=10, pady=10)
        self.load_btn.grid(row=1, column=0, sticky="ew", padx=(10,5), pady=5)
        self.export_btn.grid(row=1, column=1, sticky="ew", padx=5, pady=5)
        self.reset_btn.grid(row=1, column=2, columnspan=2, sticky="ew", padx=(5,10), pady=5)
        self.run_btn.grid(row=2, column=0, sticky="ew", padx=(10,5), pady=5)
        self.step_btn.grid(row=2, column=1, sticky="ew", padx=5, pady=5)
        self.forward_chk.grid(row=2, column=2, columnspan=2, sticky="w", padx=15)
        self.speed_slider.grid(row=3, column=0, columnspan=3, sticky="ew", padx=10, pady=5)
        self.speed_lbl.grid(row=3, column=3, sticky="w", padx=5)
        self.vis_frame.grid_rowconfigure(0, weight=1)
        self.vis_frame.grid_columnconfigure(0, weight=1)
        self.canvas.grid(row=0, column=0, sticky="nsew", padx=10, pady=10)
        self.right_tabs.grid(row=1, column=1, sticky="nsew", padx=(4,8), pady=4)
        self.reg_list.pack(fill="both", expand=True, padx=5, pady=5)
        self.mem_list.pack(fill="both", expand=True, padx=5, pady=5)
        self.stats_text.pack(fill="both", expand=True, padx=5, pady=5)
        self.log_txt.pack(fill="both", expand=True, padx=5, pady=5)
        self.inspector.grid(row=2, column=0, columnspan=2, sticky="nsew", padx=8, pady=(4,8))
        self.inspector.grid_columnconfigure(0, weight=1)
        self.inspector_lbl.grid(row=0, column=0, sticky="w", padx=12, pady=(5,0))
        self.inspector_text.grid(row=1, column=0, sticky="nsew", padx=12, pady=(0,12))
    def _bind_shortcuts(self):
        self.bind("<space>", lambda e: self._toggle_play())
        self.bind("<Return>", lambda e: self._on_step())
    def _on_speed_change(self, *args):
        self.speed_lbl.configure(text=f"Speed: {self.speed.get():.1f}x")
    def _on_load_program(self, initial=False):
        if self.playing:
            self._toggle_play()
        text = self.program_txt.get("1.0", "end").strip().splitlines()
        lines = [l.partition("#")[0].strip() for l in text if l.strip()]
        self.engine.load_program(lines)
        self.engine.reset_state(keep_regs=False)
        self.canvas.token_positions = {}
        self._refresh_side_panels()
        if not initial:
            messagebox.showinfo("Program Loaded", f"Loaded {len(self.engine.program)} instructions.")
    def _on_export_log(self):
        if not self.engine.log:
            messagebox.showwarning("Export Failed", "No log data to export. Run the simulation first.")
            return
        path = filedialog.asksaveasfilename(defaultextension=".csv", filetypes=[("CSV files", "*.csv")])
        if not path:
            return
        try:
            with open(path, "w", newline="", encoding="utf-8") as f:
                writer = csv.writer(f)
                writer.writerow(["cycle", "type", "id", "instr", "extra"])
                for entry in self.engine.log:
                    c = entry.get("cycle")
                    for a in entry.get("actions", []):
                        typ = a.get("type")
                        rid = a.get("id", "")
                        instr = a.get("instr", "")
                        extra = {k:v for k,v in a.items() if k not in ("type","id","instr")}
                        writer.writerow([c, typ, rid, instr, json.dumps(extra)])
            messagebox.showinfo("Exported", f"Log exported to {path}")
        except Exception as e:
            messagebox.showerror("Error", str(e))
    def _on_reset(self):
        if self.playing:
            self._toggle_play()
        self.engine.reset_state(keep_regs=False)
        self.canvas.token_positions = {}
        self._refresh_side_panels()
        self.canvas.draw()
        self.inspector_text.configure(state=tk.NORMAL)
        self.inspector_text.delete("1.0", "end")
        self.inspector_text.insert("1.0", "Hover over a token to see details.")
        self.inspector_text.configure(state=tk.DISABLED)
        self.log_txt.delete("1.0", "end")
    def _on_step(self):
        cycle_events = self.engine.step(use_forwarding=self.use_forwarding.get())
        self.canvas.token_positions = {t.id: (t.x, t.y) for t in self.engine.tokens}
        self._append_log(cycle_events)
        self._refresh_side_panels()
        self.canvas.draw()
    def _toggle_play(self):
        self.playing = not self.playing
        if self.playing:
            self.run_btn.configure(text="⏸ Pause")
            t = threading.Thread(target=self._auto_run_loop, daemon=True)
            t.start()
        else:
            self.run_btn.configure(text="▶ Play")
    def _auto_run_loop(self):
        while self.playing and (self.engine.can_fetch() or any(not t.is_completed() for t in self.engine.tokens)):
            start = time.time()
            events = self.engine.step(use_forwarding=self.use_forwarding.get())
            self._append_log(events)
            self.canvas.token_positions = {t.id: (t.x, t.y) for t in self.engine.tokens}
            self._refresh_side_panels()
            self.canvas.draw()
            spd = max(0.1, self.speed.get())
            elapsed = time.time() - start
            to_wait = max(0.0, (1.0 / spd) - elapsed)
            time.sleep(to_wait)
        self.playing = False
        self.run_btn.configure(text="▶ Play")
    def update_inspector(self, token: Optional[Token]):
        self.inspector_text.configure(state=tk.NORMAL)
        self.inspector_text.delete("1.0", "end")
        if token is None:
            self.inspector_text.insert("1.0", "Hover over an instruction in the pipeline to see details.")
        else:
            instr = token.instr
            lines = [
                f"Instruction: {instr.raw}",
                f"Op: {instr.op}",
                f"Dst: {instr.dst}",
                f"Src1: {instr.src1}",
                f"Src2: {instr.src2}",
                f"Imm: {instr.imm}",
                f"Stage index: {token.stage_idx}",
                f"Last result: {instr.result}"
            ]
            self.inspector_text.insert("1.0", "\n".join(lines))
        self.inspector_text.configure(state=tk.DISABLED)
    def _append_log(self, cycle_events: Dict):
        self.log_txt.insert("end", f"Cycle {cycle_events.get('cycle')}\n")
        for a in cycle_events.get("actions", []):
            typ = a.get("type")
            instr = a.get("instr", "")
            extra = {k:v for k,v in a.items() if k not in ("type","instr","id")}
            self.log_txt.insert("end", f"  - {typ}: {instr} {extra}\n")
        self.log_txt.see("end")
    def _refresh_side_panels(self):
        self.reg_list.delete(0, tk.END)
        for r in sorted(self.registers.keys(), key=lambda x:int(x[1:])):
            self.reg_list.insert(tk.END, f"{r}: {self.registers[r]}")
        self.mem_list.delete(0, tk.END)
        for i in range(len(self.memory)):
            self.mem_list.insert(tk.END, f"M[{i:03}]: {self.memory[i]}")
        self.stats_text.configure(state=tk.NORMAL)
        self.stats_text.delete("1.0", "end")
        stats_lines = [
            f"Cycle: {self.engine.cycle}",
            f"PC: {self.engine.pc}",
            f"Tokens in pipeline: {len(self.engine.tokens)}",
            f"Completed instructions: {self.engine.completed_instrs}",
            f"Stalls: {self.engine.stalls}",
            f"Forwards: {self.engine.forwards}",
        ]
        self.stats_text.insert("1.0", "\n".join(stats_lines))
        self.stats_text.configure(state=tk.DISABLED)
    def _animation_tick(self):
        left = 20
        prog_w = INSTR_COL_W - 20
        for idx, token in enumerate(self.engine.tokens):
            row_y = 70 + idx * (TOKEN_H + 8)
            stage_idx = token.stage_idx if not token.bubble else token.stage_idx
            stage_idx = max(0, stage_idx)
            sx = left + prog_w + 30 + stage_idx * (STAGE_COL_W + 10)
            tx = sx + (STAGE_COL_W - TOKEN_W) / 2
            ty = row_y
            if token.id not in getattr(self.canvas, "token_positions", {}):
                start_x = left + 12
                start_y = ty
                token.x, token.y = start_x, start_y
                self.canvas.token_positions[token.id] = (start_x, start_y)
            cur_x, cur_y = self.canvas.token_positions[token.id]
            nx = lerp(cur_x, tx, 0.33)
            ny = lerp(cur_y, ty, 0.33)
            token.x, token.y = nx, ny
            self.canvas.token_positions[token.id] = (nx, ny)
        self.canvas.draw()
        self.after(int(1000 / 30), self._animation_tick)

if __name__ == "__main__":
    app = PipelineApp()
    app.mainloop()