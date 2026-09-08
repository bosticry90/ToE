"""Documentation-only regression and scratch algebra checks; no VPC promotion."""
import copy
import json
import unittest

import sympy as s

import validate_packet as packet


class PacketChecks(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.win, cls.blobs = packet.load_evidence()

    def test_altered_output_rejected(self):
        changed = copy.deepcopy(self.win)
        changed["verification_receipt"]["outputs"][0]["value"]["unexpected"] = True
        with self.assertRaisesRegex(ValueError, "Value binding"):
            packet.scope_projection(changed, self.blobs)

    def test_altered_request_rejected(self):
        changed = copy.deepcopy(self.win)
        changed["request"]["inputs"]["unexpected"] = "mutation"
        with self.assertRaisesRegex(ValueError, "Request binding"):
            packet.scope_projection(changed, self.blobs)

    def test_missing_challenge_rejected(self):
        changed = copy.deepcopy(self.win)
        changed["challenge_packets"].pop()
        with self.assertRaisesRegex(ValueError, "Challenge census"):
            packet.scope_projection(changed, self.blobs)

    def test_wrong_archive_identity_rejected(self):
        manifest = json.loads((packet.HERE / "manifest.json").read_bytes())
        manifest["archive"]["sha256"] = "0" * 64
        with self.assertRaisesRegex(ValueError, "Archive SHA256"):
            packet.archive_checks(manifest, self.win)

    def test_qexp_coefficients(self):
        x, p = s.symbols("x p", real=True)
        expression = s.exp(s.log(1 + p * x) / p)
        expected = 1 + x + (1 - p) * x**2 / 2 + (1 - p) * (1 - 2 * p) * x**3 / 6
        self.assertEqual(s.simplify(s.series(expression, x, 0, 4).removeO() - expected), 0)

    def test_qexp_log_limit(self):
        x, p = s.symbols("x p", real=True)
        self.assertEqual(s.limit(s.log(1 + p * x) / p, p, 0), x)

    def test_linear_member(self):
        x = s.symbols("x", real=True)
        self.assertEqual(s.exp(s.log(1 + x)), 1 + x)

    def test_sqrt_member(self):
        x = s.symbols("x", real=True)
        self.assertEqual(s.exp(s.log(1 + 2 * x) / 2), s.sqrt(1 + 2 * x))

    def test_half_interval_coefficient(self):
        T, total, m, g, hbar = s.symbols("T total m g hbar", nonzero=True)
        phase = -m * g**2 * T**3 / (3 * hbar)
        self.assertEqual(s.simplify(phase.subs(T, total / 2) + m * g**2 * total**3 / (24 * hbar)), 0)


if __name__ == "__main__":
    unittest.main(verbosity=2)
