"""Regression tests for the verifier's shared child-process cleanup."""
from concurrent.futures import ThreadPoolExecutor
import sys
import tempfile
import time
from pathlib import Path
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from scripts.build_lean_modules import BuildProcesses
from scripts.replay_lean_modules import LeanProcesses


class ProcessGroupsTests(unittest.TestCase):
    def test_exited_leaders_do_not_leave_descendants(self):
        with tempfile.TemporaryDirectory() as directory:
            marker = Path(directory) / "survived"
            child = f"import time; from pathlib import Path; time.sleep(0.5); Path({str(marker)!r}).touch()"
            parent = f"import subprocess, sys; subprocess.Popen([sys.executable, '-c', {child!r}], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)"
            for processes in (BuildProcesses(), LeanProcesses([sys.executable])):
                with self.subTest(processes=type(processes).__name__):
                    if isinstance(processes, BuildProcesses):
                        self.assertEqual(processes.run([sys.executable, "-c", parent]), 0)
                    else:
                        self.assertEqual(processes.run(["-c", parent]), "")
                    time.sleep(0.8)
                    self.assertFalse(marker.exists(), "a descendant survived its scheduler process")

    def test_stop_cancels_active_builds_and_rejects_new_launches(self):
        processes = BuildProcesses()
        with ThreadPoolExecutor(max_workers=2) as pool:
            pending = [pool.submit(processes.run, [sys.executable, "-c", "import time; time.sleep(30)"])
                       for _ in range(2)]
            deadline = time.monotonic() + 5
            while time.monotonic() < deadline:
                with processes.lock:
                    if len(processes.active) == 2:
                        break
                time.sleep(0.01)
            else:
                processes.stop()
                self.fail("build processes did not start")
            processes.stop()
            for result in pending:
                self.assertNotEqual(result.result(timeout=5), 0)
        processes.stop()  # Repeated cancellation is safe.
        with self.assertRaisesRegex(RuntimeError, "Build cancelled"):
            processes.run([sys.executable, "-c", "pass"])

    def test_failed_worker_cancels_future_launches(self):
        processes = LeanProcesses([sys.executable])
        with self.assertRaisesRegex(ValueError, "Trusted Lean worker failed"):
            processes.run(["-c", "raise SystemExit(7)"])
        with self.assertRaisesRegex(ValueError, "launch cancelled"):
            processes.run(["-c", "pass"])


if __name__ == "__main__":
    unittest.main()
