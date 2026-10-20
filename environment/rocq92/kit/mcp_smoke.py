#!/usr/bin/env python3
"""Exercise a fresh, privately owned stdio MCP process; no model/API calls."""
import json
import os
from pathlib import Path
import selectors
import subprocess
import sys
import time

source = str(Path(sys.argv[1]).resolve())
process = subprocess.Popen(["rocq-mcp-evolve"], stdin=subprocess.PIPE,
                           stdout=subprocess.PIPE, bufsize=0)
selector = selectors.DefaultSelector()
selector.register(process.stdout, selectors.EVENT_READ)
buffer = b""
sequence = 0


def send(method, params, notification=False):
    global sequence, buffer
    sequence += 1
    message = {"jsonrpc": "2.0", "method": method, "params": params}
    if not notification:
        message["id"] = sequence
    process.stdin.write((json.dumps(message) + "\n").encode())
    if notification:
        return None
    deadline = time.monotonic() + 120
    while time.monotonic() < deadline:
        if b"\n" not in buffer:
            if not selector.select(timeout=1):
                continue
            data = os.read(process.stdout.fileno(), 65536)
            if not data:
                raise RuntimeError("MCP closed stdout")
            buffer += data
        while b"\n" in buffer:
            line, buffer = buffer.split(b"\n", 1)
            response = json.loads(line)
            if response.get("id") != sequence:
                continue
            if "error" in response or response.get("result", {}).get("isError"):
                raise RuntimeError(response)
            return response["result"]
    raise TimeoutError(method)


try:
    send("initialize", {"protocolVersion": "2024-11-05", "capabilities": {},
                        "clientInfo": {"name": "graph-theory-rocq-smoke", "version": "1"}})
    send("notifications/initialized", {}, notification=True)
    names = {t["name"] for t in send("tools/list", {})["tools"]}
    assert {"open", "auto_close", "step"} <= names, names
    send("tools/call", {"name": "open", "arguments": {
        "file": source, "theorem": "aws_environment_smoke"}})
    result = send("tools/call", {"name": "auto_close", "arguments": {}})
    if "PROOF COMPLETE" not in json.dumps(result):
        result = send("tools/call", {"name": "step", "arguments": {
            "text": "intros; reflexivity."}})
    assert "PROOF COMPLETE" in json.dumps(result), result
    print("PASS: fresh rocq-evolve initialize, tools/list, open and completed proof")
finally:
    selector.close()
    process.terminate()
    try:
        process.wait(timeout=5)
    except subprocess.TimeoutExpired:
        process.kill()
        process.wait()
