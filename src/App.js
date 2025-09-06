import React, { useMemo, useState, useEffect, useRef } from "react";

/**
 * OS Simulator (Single-File React App)
 * - CPU Scheduling: FCFS, SJF, SRTF, Priority, Round Robin
 * - Page Replacement: FIFO, LRU
 * - Disk Scheduling: FCFS, SSTF, SCAN, C-SCAN
 * - Deadlock (Banker's): simple checker with preset sample
 * - Producer–Consumer (Semaphore demo): simple animated buffer
 * - File System (toy): create folders/files and show simplified FAT/inode
 *
 * Design:
 * - TailwindCSS utility classes
 * - Mobile friendly, grid layout, rounded cards, soft shadows
 *
 * Notes:
 * - Everything is client-side. No backend required.
 * - Algorithms are implemented in plain JS for clarity.
 */

/******************** UTILS ********************/
const rnd = (min, max) => Math.floor(Math.random() * (max - min + 1)) + min;
const sum = (arr) => arr.reduce((a,b)=>a+b,0);

/******************** LAYOUT ********************/
function Card({ title, children, right }) {
  return (
    <div className="bg-white/90 backdrop-blur shadow-sm rounded-2xl p-4 border border-slate-200">
      <div className="flex items-center justify-between mb-3 gap-3">
        <h2 className="text-lg font-semibold tracking-tight text-slate-800">{title}</h2>
        {right}
      </div>
      {children}
    </div>
  );
}

function Tabs({ tabs, value, onChange }) {
  return (
    <div className="flex flex-wrap gap-2">
      {tabs.map((t) => (
        <button
          key={t}
          onClick={() => onChange(t)}
          className={`px-3 py-1.5 rounded-xl border text-sm font-medium transition ${
            value === t
              ? "bg-slate-900 text-white border-slate-900"
              : "bg-white text-slate-700 border-slate-200 hover:bg-slate-50"
          }`}
        >
          {t}
        </button>
      ))}
    </div>
  );
}

function Pill({ children }) {
  return (
    <span className="px-2 py-0.5 rounded-full bg-slate-100 text-slate-700 text-xs border border-slate-200">
      {children}
    </span>
  );
}

/******************** CPU SCHEDULING ********************/
// Shared helpers
function clone(arr){ return JSON.parse(JSON.stringify(arr)); }

function ganttColor(i){
  const palette = [
    "#93c5fd", "#fca5a5", "#fdba74", "#86efac", "#c4b5fd",
    "#f9a8d4", "#a5f3fc", "#fde68a", "#ddd6fe", "#bbf7d0",
  ];
  return palette[i % palette.length];
}

// Metrics calculator
function computeMetrics(schedule, processes){
  // schedule: array of {pid, start, end}
  const procs = Object.fromEntries(processes.map(p=>[p.pid, {...p}]));
  const firstStart = schedule.length? schedule[0].start : 0;
  const lastEnd = schedule.length? schedule[schedule.length-1].end : 0;

  const metrics = processes.map(p=>({
    pid: p.pid,
    arrival: p.arrival,
    burst: p.burst,
    priority: p.priority ?? 0,
    start: null,
    completion: null,
    waiting: 0,
    turnaround: 0,
    response: null,
  }));
  const mBy = Object.fromEntries(metrics.map(m=>[m.pid,m]));

  // compute start, completion, response
  for(const seg of schedule){
    const m = mBy[seg.pid];
    if(m){
      if(m.start === null) m.start = seg.start;
      m.completion = seg.end; // last time we see the pid
    }
  }
  // waiting, turnaround, response
  metrics.forEach(m=>{
    m.turnaround = (m.completion ?? m.arrival) - m.arrival;
    // total executed time
    const executed = schedule.filter(s=>s.pid===m.pid).reduce((a,b)=>a+(b.end-b.start),0);
    m.waiting = m.turnaround - executed;
    m.response = (m.start ?? m.arrival) - m.arrival;
  });

  const totalBurst = processes.reduce((a,b)=>a+b.burst,0);
  const utilization = lastEnd===0?0: (totalBurst/ (lastEnd-firstStart)) * 100;
  const throughput = lastEnd===0?0: processes.length / (lastEnd-firstStart);

  return { metrics, utilization, throughput };
}

// Algorithms
function fcfs(processes){
  const procs = clone(processes).sort((a,b)=> a.arrival - b.arrival);
  let t = 0; const schedule = [];
  for(const p of procs){
    t = Math.max(t, p.arrival);
    schedule.push({ pid:p.pid, start:t, end:t+p.burst });
    t += p.burst;
  }
  return schedule;
}

function sjf(processes){
  const ready = []; let t = Math.min(...processes.map(p=>p.arrival));
  const procs = clone(processes); const schedule=[]; const seen = new Set();
  while(seen.size < procs.length){
    for(const p of procs){ if(!seen.has(p.pid) && p.arrival<=t && !ready.find(r=>r.pid===p.pid)) ready.push(p); }
    if(ready.length===0){ t++; continue; }
    // pick shortest burst
    ready.sort((a,b)=> a.burst - b.burst);
    const p = ready.shift();
    schedule.push({ pid:p.pid, start:t, end:t+p.burst});
    t += p.burst; seen.add(p.pid);
  }
  return schedule;
}

function srtf(processes){
  const procs = clone(processes).map(p=>({...p, remaining:p.burst}));
  let t = Math.min(...procs.map(p=>p.arrival));
  const schedule=[];
  let current=null;
  while(procs.some(p=>p.remaining>0)){
    const ready = procs.filter(p=>p.arrival<=t && p.remaining>0);
    if(ready.length===0){ t++; continue; }
    ready.sort((a,b)=> a.remaining - b.remaining);
    const next = ready[0];
    if(!current || current.pid!==next.pid){
      if(current && schedule.length && schedule[schedule.length-1].end===null){
        schedule[schedule.length-1].end = t;
      }
      schedule.push({ pid: next.pid, start: t, end: null });
      current = next;
    }
    // run 1 unit
    current.remaining--; t++;
    if(current.remaining===0){
      schedule[schedule.length-1].end = t; current = null;
    }
  }
  return schedule;
}

function priorityNonPreemptive(processes){
  const procs = clone(processes); let t = Math.min(...procs.map(p=>p.arrival));
  const done = new Set(); const schedule=[];
  while(done.size < procs.length){
    const ready = procs.filter(p=>p.arrival<=t && !done.has(p.pid));
    if(ready.length===0){ t++; continue; }
    ready.sort((a,b)=> (a.priority??0) - (b.priority??0)); // lower = higher priority
    const p = ready[0];
    schedule.push({pid:p.pid, start:t, end:t+p.burst});
    t += p.burst; done.add(p.pid);
  }
  return schedule;
}

function roundRobin(processes, quantum=2){
  const procs = clone(processes).map(p=>({...p, remaining:p.burst})).sort((a,b)=>a.arrival-b.arrival);
  const q = quantum;
  const schedule=[]; const ready=[]; let t = procs[0]?.arrival ?? 0; let i=0;
  while(ready.length>0 || i<procs.length){
    // enqueue newly arrived
    while(i<procs.length && procs[i].arrival<=t){ ready.push(procs[i]); i++; }
    if(ready.length===0){ t = procs[i]?.arrival ?? t+1; continue; }
    const p = ready.shift();
    const run = Math.min(q, p.remaining);
    schedule.push({ pid:p.pid, start:t, end:t+run });
    p.remaining -= run; t += run;
    // enqueue arrivals during this run
    while(i<procs.length && procs[i].arrival<=t){ ready.push(procs[i]); i++; }
    if(p.remaining>0) ready.push(p);
  }
  return schedule;
}

function CPUScheduler(){
  const [algo, setAlgo] = useState("FCFS");
  const [quantum, setQuantum] = useState(2);
  const [rows, setRows] = useState([
    { pid:"P1", arrival:0, burst:7, priority:2 },
    { pid:"P2", arrival:2, burst:4, priority:1 },
    { pid:"P3", arrival:4, burst:1, priority:3 },
    { pid:"P4", arrival:5, burst:4, priority:2 },
  ]);

  const schedule = useMemo(()=>{
    if(algo==="FCFS") return fcfs(rows);
    if(algo==="SJF") return sjf(rows);
    if(algo==="SRTF") return srtf(rows);
    if(algo==="PRIORITY") return priorityNonPreemptive(rows);
    if(algo==="RR") return roundRobin(rows, quantum);
    return [];
  }, [rows, algo, quantum]);

  const { metrics, utilization, throughput } = useMemo(()=>computeMetrics(schedule, rows),[schedule, rows]);

  const minTime = schedule.length? Math.min(...schedule.map(s=>s.start)) : 0;
  const maxTime = schedule.length? Math.max(...schedule.map(s=>s.end)) : 0;
  const totalSpan = Math.max(1, maxTime - minTime);

  const addRow = () => setRows((r)=>[...r, { pid:`P${r.length+1}`, arrival:rnd(0,6), burst:rnd(1,8), priority:rnd(1,3) }]);
  const reset = () => setRows([
    { pid:"P1", arrival:0, burst:7, priority:2 },
    { pid:"P2", arrival:2, burst:4, priority:1 },
    { pid:"P3", arrival:4, burst:1, priority:3 },
    { pid:"P4", arrival:5, burst:4, priority:2 },
  ]);

  const update = (i, key, val) => setRows((r)=>{
    const x = [...r];
    x[i] = { ...x[i], [key]: (key==="pid"? String(val) : Number(val)) };
    return x;
  });

  return (
    <Card title="CPU Scheduling">
      <div className="flex flex-col gap-4">
        <div className="flex flex-wrap items-end gap-3">
          <div className="flex items-center gap-2">
            <span className="text-sm text-slate-700">Algorithm</span>
            <select value={algo} onChange={(e)=>setAlgo(e.target.value)} className="border rounded-lg px-2 py-1">
              <option>FCFS</option>
              <option>SJF</option>
              <option>SRTF</option>
              <option value="PRIORITY">Priority (Non-Preemptive)</option>
              <option value="RR">RR (Round Robin)</option>
            </select>
          </div>
          {algo==="RR" && (
            <div className="flex items-center gap-2">
              <span className="text-sm text-slate-700">Quantum</span>
              <input type="number" min={1} value={quantum} onChange={(e)=>setQuantum(Number(e.target.value)||1)} className="border rounded-lg px-2 py-1 w-20" />
            </div>
          )}
          <div className="ml-auto flex gap-2">
            <button onClick={addRow} className="px-3 py-1.5 rounded-lg border bg-white hover:bg-slate-50">Add Process</button>
            <button onClick={reset} className="px-3 py-1.5 rounded-lg border bg-white hover:bg-slate-50">Reset</button>
          </div>
        </div>

        {/* Table */}
        <div className="overflow-auto border rounded-xl">
          <table className="min-w-full text-sm">
            <thead className="bg-slate-50 text-slate-700">
              <tr>
                {['PID','Arrival','Burst','Priority',''].map(h=> <th key={h} className="text-left px-3 py-2 border-b">{h}</th>)}
              </tr>
            </thead>
            <tbody>
              {rows.map((row,i)=> (
                <tr key={i} className="hover:bg-slate-50">
                  <td className="px-3 py-2 border-b">
                    <input value={row.pid} onChange={e=>update(i,'pid', e.target.value)} className="w-20 border rounded px-2 py-1" />
                  </td>
                  <td className="px-3 py-2 border-b">
                    <input type="number" value={row.arrival} onChange={e=>update(i,'arrival', e.target.value)} className="w-20 border rounded px-2 py-1" />
                  </td>
                  <td className="px-3 py-2 border-b">
                    <input type="number" value={row.burst} onChange={e=>update(i,'burst', e.target.value)} className="w-20 border rounded px-2 py-1" />
                  </td>
                  <td className="px-3 py-2 border-b">
                    <input type="number" value={row.priority} onChange={e=>update(i,'priority', e.target.value)} className="w-20 border rounded px-2 py-1" />
                  </td>
                  <td className="px-3 py-2 border-b">
                    <button onClick={()=> setRows(r=> r.filter((_,j)=>j!==i))} className="text-red-600 hover:underline">Delete</button>
                  </td>
                </tr>
              ))}
            </tbody>
          </table>
        </div>

        {/* Gantt */}
        <div>
          <div className="mb-2 text-sm text-slate-700">Gantt Chart</div>
          <div className="w-full border rounded-xl p-2 overflow-x-auto">
            <div className="relative min-w-[600px]">
              {schedule.map((seg, idx)=>{
                const left = ((seg.start - minTime) / totalSpan) * 100;
                const width = ((seg.end - seg.start) / totalSpan) * 100;
                return (
                  <div key={idx} className="absolute top-0 h-10 rounded-md flex items-center justify-center text-xs font-medium"
                    style={{ left: `${left}%`, width: `${width}%`, background: ganttColor(rows.findIndex(r=>r.pid===seg.pid)) }}>
                    {seg.pid} [{seg.start}-{seg.end}]
                  </div>
                );
              })}
              <div className="h-10" />
            </div>
          </div>
        </div>

        {/* Metrics */}
        <div className="overflow-auto border rounded-xl">
          <table className="min-w-full text-sm">
            <thead className="bg-slate-50 text-slate-700">
              <tr>
                {['PID','Arrival','Burst','Start','Completion','Waiting','Turnaround','Response'].map(h=> <th key={h} className="text-left px-3 py-2 border-b">{h}</th>)}
              </tr>
            </thead>
            <tbody>
              {metrics.map((m,i)=> (
                <tr key={i} className="hover:bg-slate-50">
                  <td className="px-3 py-2 border-b">{m.pid}</td>
                  <td className="px-3 py-2 border-b">{m.arrival}</td>
                  <td className="px-3 py-2 border-b">{m.burst}</td>
                  <td className="px-3 py-2 border-b">{m.start}</td>
                  <td className="px-3 py-2 border-b">{m.completion}</td>
                  <td className="px-3 py-2 border-b">{m.waiting}</td>
                  <td className="px-3 py-2 border-b">{m.turnaround}</td>
                  <td className="px-3 py-2 border-b">{m.response}</td>
                </tr>
              ))}
            </tbody>
          </table>
        </div>
        <div className="flex flex-wrap gap-3 text-sm text-slate-700">
          <Pill>CPU Utilization: {utilization.toFixed(1)}%</Pill>
          <Pill>Throughput: {throughput.toFixed(2)} / time-unit</Pill>
          <Pill>Segments: {schedule.length}</Pill>
        </div>
      </div>
    </Card>
  );
}

/******************** PAGE REPLACEMENT ********************/
function fifoPage(refs, frames){
  const frameArr = Array(frames).fill(null);
  const timeline = []; let ptr=0; let faults=0;
  refs.forEach((p,i)=>{
    const hit = frameArr.includes(p);
    if(!hit){ faults++; frameArr[ptr] = p; ptr = (ptr+1)%frames; }
    timeline.push({ step:i, page:p, frames:[...frameArr], hit });
  });
  return { timeline, faults };
}

function lruPage(refs, frames){
  const frameArr = []; const lastUsed = new Map();
  const timeline=[]; let faults=0;
  refs.forEach((p,i)=>{
    const idx = frameArr.indexOf(p);
    if(idx!==-1){ // hit
      lastUsed.set(p, i);
      timeline.push({ step:i, page:p, frames:[...frameArr, ...Array(frames-frameArr.length).fill(null)], hit:true });
      return;
    }
    faults++;
    if(frameArr.length<frames){
      frameArr.push(p);
    } else {
      // evict least recently used
      let lruPage = frameArr[0], lruT = lastUsed.get(lruPage) ?? -1;
      for(const q of frameArr){
        const t = lastUsed.get(q) ?? -1;
        if(t<lruT){ lruPage=q; lruT=t; }
      }
      const evIdx = frameArr.indexOf(lruPage);
      frameArr[evIdx] = p;
    }
    lastUsed.set(p, i);
    timeline.push({ step:i, page:p, frames:[...frameArr], hit:false });
  });
  // Normalize frames length per row
  timeline.forEach(t=>{ if(t.frames.length<frames){ t.frames = [...t.frames, ...Array(frames-t.frames.length).fill(null)]; } });
  return { timeline, faults };
}

function PageReplacement(){
  const [frames, setFrames] = useState(3);
  const [input, setInput] = useState("7 0 1 2 0 3 0 4 2 3 0 3 2");
  const refs = useMemo(()=> input.trim().split(/\s+/).filter(Boolean).map(Number), [input]);
  const { timeline:fifoTL, faults:fifoF } = useMemo(()=> fifoPage(refs, frames), [refs, frames]);
  const { timeline:lruTL, faults:lruF } = useMemo(()=> lruPage(refs, frames), [refs, frames]);

  return (
    <Card title="Page Replacement">
      <div className="flex flex-col gap-4">
        <div className="flex flex-wrap items-end gap-3">
          <div>
            <div className="text-sm text-slate-700">Reference String</div>
            <input value={input} onChange={e=>setInput(e.target.value)} className="border rounded-lg px-3 py-2 w-[420px] max-w-full" />
          </div>
          <div>
            <div className="text-sm text-slate-700">Frames</div>
            <input type="number" min={1} value={frames} onChange={e=>setFrames(Number(e.target.value)||1)} className="border rounded-lg px-3 py-2 w-24" />
          </div>
        </div>

        <div className="grid md:grid-cols-2 gap-4">
          {[{name:"FIFO", tl:fifoTL, f:fifoF}, {name:"LRU", tl:lruTL, f:lruF}].map(({name, tl, f})=> (
            <div key={name} className="border rounded-xl overflow-auto">
              <div className="px-3 py-2 bg-slate-50 flex items-center justify-between">
                <div className="font-medium text-slate-800">{name}</div>
                <Pill>Faults: {f}</Pill>
              </div>
              <table className="min-w-full text-sm">
                <thead>
                  <tr>
                    <th className="text-left px-3 py-2 border-b">Step</th>
                    <th className="text-left px-3 py-2 border-b">Page</th>
                    <th className="text-left px-3 py-2 border-b">Frames</th>
                    <th className="text-left px-3 py-2 border-b">Hit?</th>
                  </tr>
                </thead>
                <tbody>
                  {tl.map((row)=> (
                    <tr key={`${name}-${row.step}`} className="hover:bg-slate-50">
                      <td className="px-3 py-2 border-b">{row.step}</td>
                      <td className="px-3 py-2 border-b">{row.page}</td>
                      <td className="px-3 py-2 border-b">
                        <div className="flex gap-2">
                          {row.frames.map((f,i)=> (
                            <div key={i} className={`w-10 h-8 rounded-md border flex items-center justify-center ${f===null? 'bg-slate-50 text-slate-400':'bg-white'}`}>{f??'-'}</div>
                          ))}
                        </div>
                      </td>
                      <td className="px-3 py-2 border-b">{row.hit? 'Yes':'No'}</td>
                    </tr>
                  ))}
                </tbody>
              </table>
            </div>
          ))}
        </div>
      </div>
    </Card>
  );
}

/******************** DISK SCHEDULING ********************/
function pathFCFS(queue, head){ return [head, ...queue]; }
function pathSSTF(queue, head){
  const q = [...queue]; let cur = head; const path=[cur];
  while(q.length){
    let idx=0, best=Infinity;
    q.forEach((v,i)=>{ const d=Math.abs(v-cur); if(d<best){best=d; idx=i;} });
    cur = q.splice(idx,1)[0]; path.push(cur);
  }
  return path;
}
function pathSCAN(queue, head, max=199){
  const below = queue.filter(x=>x<head).sort((a,b)=>a-b);
  const above = queue.filter(x=>x>=head).sort((a,b)=>a-b);
  return [head, ...above, max, ...below.reverse()];
}
function pathCSCAN(queue, head, max=199){
  const above = queue.filter(x=>x>=head).sort((a,b)=>a-b);
  const below = queue.filter(x=>x<head).sort((a,b)=>a-b);
  return [head, ...above, max, 0, ...below];
}

function totalSeek(path){ let s=0; for(let i=1;i<path.length;i++) s += Math.abs(path[i]-path[i-1]); return s; }

function DiskScheduling(){
  const [algo, setAlgo] = useState("FCFS");
  const [queueStr, setQueueStr] = useState("98 183 37 122 14 124 65 67");
  const [head, setHead] = useState(53);
  const [maxCyl, setMaxCyl] = useState(199);

  const queue = useMemo(()=> queueStr.trim().split(/\s+/).filter(Boolean).map(Number), [queueStr]);
  const path = useMemo(()=>{
    if(algo==="FCFS") return pathFCFS(queue, head);
    if(algo==="SSTF") return pathSSTF(queue, head);
    if(algo==="SCAN") return pathSCAN(queue, head, maxCyl);
    if(algo==="C-SCAN") return pathCSCAN(queue, head, maxCyl);
    return [];
  }, [algo, queue, head, maxCyl]);

  return (
    <Card title="Disk Scheduling">
      <div className="flex flex-col gap-4">
        <div className="flex flex-wrap items-end gap-3">
          <div className="flex items-center gap-2">
            <span className="text-sm text-slate-700">Algorithm</span>
            <select value={algo} onChange={e=>setAlgo(e.target.value)} className="border rounded-lg px-2 py-1">
              <option>FCFS</option>
              <option>SSTF</option>
              <option>SCAN</option>
              <option>C-SCAN</option>
            </select>
          </div>
          <div>
            <div className="text-sm text-slate-700">Queue</div>
            <input value={queueStr} onChange={e=>setQueueStr(e.target.value)} className="border rounded-lg px-3 py-2 w-[420px] max-w-full" />
          </div>
          <div>
            <div className="text-sm text-slate-700">Head</div>
            <input type="number" value={head} onChange={e=>setHead(Number(e.target.value)||0)} className="border rounded-lg px-3 py-2 w-24" />
          </div>
          <div>
            <div className="text-sm text-slate-700">Max Cylinder</div>
            <input type="number" value={maxCyl} onChange={e=>setMaxCyl(Number(e.target.value)||0)} className="border rounded-lg px-3 py-2 w-28" />
          </div>
        </div>

        <div className="border rounded-xl p-4 overflow-x-auto">
          <div className="min-w-[600px]">
            <div className="text-sm text-slate-700 mb-2">Head Movement Path (Total Seek: {totalSeek(path)})</div>
            <div className="flex items-center gap-2">
              {path.map((v,i)=> (
                <div key={i} className="flex items-center gap-2">
                  <div className="px-2 py-1 rounded-lg border bg-white text-sm">{v}</div>
                  {i<path.length-1 && <div className="w-10 h-[2px] bg-slate-300"/>}
                </div>
              ))}
            </div>
          </div>
        </div>
      </div>
    </Card>
  );
}

/******************** BANKER'S ALGORITHM (Deadlock Safety) ********************/
function isSafe(available, max, alloc){
  // available: [m], max: [n][m], alloc: [n][m]
  const n = max.length, m = available.length;
  const need = Array.from({length:n}, (_,i)=> Array.from({length:m},(_,j)=> max[i][j]-alloc[i][j]));
  const work = [...available];
  const finish = Array(n).fill(false);
  const seq = [];
  let progress=true;
  while(progress){
    progress=false;
    for(let i=0;i<n;i++) if(!finish[i]){
      let ok=true; for(let j=0;j<m;j++) if(need[i][j]>work[j]){ok=false;break;}
      if(ok){
        for(let j=0;j<m;j++) work[j]+=alloc[i][j];
        finish[i]=true; seq.push(i); progress=true;
      }
    }
  }
  const safe = finish.every(f=>f);
  return { safe, sequence: safe? seq: [], need };
}

function Bankers(){
  const [available, setAvailable] = useState([3,3,2]);
  const [maxM, setMaxM] = useState([[7,5,3],[3,2,2],[9,0,2],[2,2,2],[4,3,3]]);
  const [allocM, setAllocM] = useState([[0,1,0],[2,0,0],[3,0,2],[2,1,1],[0,0,2]]);
  const { safe, sequence, need } = useMemo(()=> isSafe(available, maxM, allocM), [available, maxM, allocM]);

  return (
    <Card title="Deadlock — Banker's Safety Check">
      <div className="flex flex-col gap-4">
        <div className="text-sm text-slate-700">Preset example (A,B,C). Edit values inline.</div>
        <div className="grid md:grid-cols-3 gap-4">
          {[{name:'Available', data:available, set:setAvailable}, {name:'Max', data:maxM, set:setMaxM}, {name:'Allocation', data:allocM, set:setAllocM}].map(({name,data,set})=> (
            <div key={name} className="border rounded-xl overflow-auto">
              <div className="px-3 py-2 bg-slate-50 font-medium">{name}</div>
              <table className="min-w-full text-sm">
                <tbody>
                  {Array.isArray(data[0])? data.map((row,i)=> (
                    <tr key={i}>
                      {row.map((v,j)=> (
                        <td key={j} className="px-2 py-1 border-b">
                          <input type="number" value={v} onChange={e=>{
                            const x = data.map(r=>[...r]); x[i][j]=Number(e.target.value)||0; set(x);
                          }} className="w-16 border rounded px-2 py-1" />
                        </td>
                      ))}
                    </tr>
                  )): (
                    <tr>
                      {data.map((v,i)=> (
                        <td key={i} className="px-2 py-1 border-b">
                          <input type="number" value={v} onChange={e=>{
                            const x=[...data]; x[i]=Number(e.target.value)||0; set(x);
                          }} className="w-16 border rounded px-2 py-1" />
                        </td>
                      ))}
                    </tr>
                  )}
                </tbody>
              </table>
            </div>
          ))}
        </div>
        <div className="flex flex-wrap gap-3 text-sm">
          <Pill>Status: {safe? 'SAFE' : 'UNSAFE'}</Pill>
          {safe && <Pill>Safe Sequence: {sequence.map(i=>`P${i}`).join(' → ')}</Pill>}
        </div>
        <div className="border rounded-xl overflow-auto">
          <div className="px-3 py-2 bg-slate-50 font-medium">Need = Max - Allocation</div>
          <table className="min-w-full text-sm">
            <tbody>
              {need.map((row,i)=> (
                <tr key={i}>
                  {row.map((v,j)=> <td key={j} className="px-3 py-2 border-b">{v}</td>)}
                </tr>
              ))}
            </tbody>
          </table>
        </div>
      </div>
    </Card>
  );
}

/******************** PRODUCER–CONSUMER (Semaphore Demo) ********************/
function ProducerConsumer(){
  const [size, setSize] = useState(5);
  const [buffer, setBuffer] = useState([]);
  const [running, setRunning] = useState(false);
  const [speed, setSpeed] = useState(600);
  const [log, setLog] = useState([]);

  useEffect(()=>{ if(!running) return; const id = setInterval(()=>{
    setBuffer((buf)=>{
      const action = Math.random()<0.5? 'produce' : 'consume';
      if(action==='produce' && buf.length < size){
        const item = rnd(10,99);
        setLog(l=>[{t:Date.now(), msg:`Produced ${item}`}, ...l].slice(0,50));
        return [...buf, item];
      }
      if(action==='consume' && buf.length>0){
        const item = buf[0];
        setLog(l=>[{t:Date.now(), msg:`Consumed ${item}`}, ...l].slice(0,50));
        return buf.slice(1);
      }
      return buf;
    });
  }, speed); return ()=>clearInterval(id); }, [running, size, speed]);

  return (
    <Card title="Producer–Consumer (Semaphore Concept Demo)">
      <div className="flex flex-col gap-4">
        <div className="flex flex-wrap items-end gap-3">
          <div>
            <div className="text-sm text-slate-700">Buffer Size</div>
            <input type="number" min={1} value={size} onChange={e=>setSize(Number(e.target.value)||1)} className="border rounded-lg px-3 py-2 w-28" />
          </div>
          <div>
            <div className="text-sm text-slate-700">Speed (ms)</div>
            <input type="number" min={100} value={speed} onChange={e=>setSpeed(Number(e.target.value)||100)} className="border rounded-lg px-3 py-2 w-28" />
          </div>
          <div className="ml-auto flex gap-2">
            <button onClick={()=>setRunning(r=>!r)} className="px-3 py-1.5 rounded-lg border bg-white hover:bg-slate-50">{running? 'Pause':'Start'}</button>
            <button onClick={()=>{setBuffer([]); setLog([]);}} className="px-3 py-1.5 rounded-lg border bg-white hover:bg-slate-50">Reset</button>
          </div>
        </div>
        <div className="flex items-center gap-2">
          {Array.from({length:size}).map((_,i)=> (
            <div key={i} className={`w-12 h-12 rounded-xl border flex items-center justify-center text-sm ${i<buffer.length? 'bg-emerald-100 border-emerald-300':'bg-white'}`}>{buffer[i]??'-'}</div>
          ))}
        </div>
        <div className="max-h-40 overflow-auto text-sm border rounded-xl p-2 bg-slate-50">
          {log.map((l,i)=> <div key={i} className="py-0.5">• {l.msg}</div>)}
        </div>
      </div>
    </Card>
  );
}

/******************** FILE SYSTEM (Toy) ********************/
function FileSystemToy(){
  const [tree, setTree] = useState({ name:"/", type:"dir", children: [] });
  const [path, setPath] = useState("");
  const [name, setName] = useState("");
  const [isDir, setIsDir] = useState(false);

  const findNode = (node, parts) => {
    if(parts.length===0) return node;
    const [p, ...rest] = parts;
    const child = node.children?.find(c=>c.name===p && c.type==='dir');
    return child? findNode(child, rest) : null;
  };

  const add = () => {
    const parts = path.split('/').filter(Boolean);
    const n = { name, type: isDir? 'dir':'file', children: isDir? []: undefined, size: isDir? undefined : rnd(1,32) };
    setTree((t)=>{
      const copy = JSON.parse(JSON.stringify(t));
      const target = findNode(copy, parts) || copy;
      target.children = target.children || [];
      if(target.children.some(c=>c.name===n.name)) return copy; // no duplicates
      target.children.push(n);
      return copy;
    });
  };

  const renderNode = (node, depth=0) => (
    <div key={node.name+depth} className="ml-2">
      <div className="flex items-center gap-2">
        <span className="font-mono text-xs text-slate-600">{Array(depth).fill('│ ').join('')}{depth>0?'├─':''}</span>
        <span className={`text-sm ${node.type==='dir'? 'font-semibold text-slate-800':'text-slate-700'}`}>{node.name}{node.type==='file'? ` (${node.size}KB)`:''}</span>
      </div>
      {node.children?.sort((a,b)=> (a.type===b.type? a.name.localeCompare(b.name) : a.type==='dir'?-1:1)).map(c=> renderNode(c, depth+1))}
    </div>
  );

  // Simplified tables
  const fatTable = [];
  const inodeTable = [];
  let blockId = 0;
  const buildTables = (node, parentInode=null) => {
    if(node.type==='file'){
      const blocks = Math.max(1, Math.ceil((node.size||1)/4));
      const first = blockId; let prev=-1;
      for(let i=0;i<blocks;i++){
        const cur = blockId++;
        fatTable.push({ block:cur, next: i<blocks-1? cur+1 : -1, file: node.name });
        prev = cur;
      }
      inodeTable.push({ inode: inodeTable.length, name: node.name, size: node.size||0, firstBlock:first });
    } else {
      const inode = inodeTable.length;
      inodeTable.push({ inode, name: node.name+'/', size: 0, firstBlock: -1 });
      node.children?.forEach(c=> buildTables(c, inode));
    }
  };
  buildTables(tree);

  return (
    <Card title="File System (Toy Model)">
      <div className="flex flex-col gap-4">
        <div className="grid md:grid-cols-3 gap-4 items-end">
          <div>
            <div className="text-sm text-slate-700">Path (dir)</div>
            <input placeholder="e.g., / or /docs" value={path} onChange={e=>setPath(e.target.value)} className="border rounded-lg px-3 py-2 w-full" />
          </div>
          <div>
            <div className="text-sm text-slate-700">Name</div>
            <input placeholder="file.txt" value={name} onChange={e=>setName(e.target.value)} className="border rounded-lg px-3 py-2 w-full" />
          </div>
          <div className="flex items-center gap-2">
            <label className="text-sm text-slate-700 flex items-center gap-2">
              <input type="checkbox" checked={isDir} onChange={e=>setIsDir(e.target.checked)} />
              Directory?
            </label>
            <button onClick={add} className="ml-auto px-3 py-2 rounded-lg border bg-white hover:bg-slate-50">Add</button>
          </div>
        </div>

        <div className="grid md:grid-cols-2 gap-4">
          <div className="border rounded-xl p-3 bg-slate-50">
            <div className="font-medium text-slate-800 mb-2">Directory Tree</div>
            <div>{renderNode(tree)}</div>
          </div>
          <div className="flex flex-col gap-4">
            <div className="border rounded-xl overflow-auto">
              <div className="px-3 py-2 bg-slate-100 font-medium">FAT (4KB blocks)</div>
              <table className="min-w-full text-sm">
                <thead>
                  <tr>
                    {['Block','Next','File'].map(h=> <th key={h} className="text-left px-3 py-2 border-b">{h}</th>)}
                  </tr>
                </thead>
                <tbody>
                  {fatTable.map((r,i)=> (
                    <tr key={i} className="hover:bg-slate-50">
                      <td className="px-3 py-2 border-b">{r.block}</td>
                      <td className="px-3 py-2 border-b">{r.next}</td>
                      <td className="px-3 py-2 border-b">{r.file}</td>
                    </tr>
                  ))}
                </tbody>
              </table>
            </div>
            <div className="border rounded-xl overflow-auto">
              <div className="px-3 py-2 bg-slate-100 font-medium">Inode Table</div>
              <table className="min-w-full text-sm">
                <thead>
                  <tr>
                    {['Inode','Name','Size(KB)','First Block'].map(h=> <th key={h} className="text-left px-3 py-2 border-b">{h}</th>)}
                  </tr>
                </thead>
                <tbody>
                  {inodeTable.map((r,i)=> (
                    <tr key={i} className="hover:bg-slate-50">
                      <td className="px-3 py-2 border-b">{r.inode}</td>
                      <td className="px-3 py-2 border-b">{r.name}</td>
                      <td className="px-3 py-2 border-b">{r.size}</td>
                      <td className="px-3 py-2 border-b">{r.firstBlock}</td>
                    </tr>
                  ))}
                </tbody>
              </table>
            </div>
          </div>
        </div>
      </div>
    </Card>
  );
}

/******************** APP SHELL ********************/
export default function OSSimulatorApp(){
  const tabs = [
    "CPU Scheduling",
    "Page Replacement",
    "Disk Scheduling",
    "Deadlock",
    "Producer–Consumer",
    "File System",
  ];
  const [tab, setTab] = useState(tabs[0]);

  return (
    <div className="min-h-screen bg-gradient-to-b from-slate-50 to-white text-slate-900 p-4 md:p-8">
      <div className="max-w-6xl mx-auto flex flex-col gap-6">
        <header className="flex flex-wrap items-center gap-4">
          <h1 className="text-2xl md:text-3xl font-bold tracking-tight">OS Simulator (Web)</h1>
          <div className="text-slate-600">CPU • Memory • Disk • Deadlock • FS</div>
          <div className="ml-auto"><Tabs tabs={tabs} value={tab} onChange={setTab} /></div>
        </header>

        {tab==="CPU Scheduling" && <CPUScheduler/>}
        {tab==="Page Replacement" && <PageReplacement/>}
        {tab==="Disk Scheduling" && <DiskScheduling/>}
        {tab==="Deadlock" && <Bankers/>}
        {tab==="Producer–Consumer" && <ProducerConsumer/>}
        {tab==="File System" && <FileSystemToy/>}

        <footer className="text-xs text-slate-500 mt-4">
           © Abdur Rob Mridha | 2025 <hr />
           Born to live
        </footer>
      </div>
    </div>
  );
}
