import signal
import re
import os
import subprocess
import unittest

DEVNULL = open(os.devnull, 'wb')


class TestCase(unittest.TestCase):
    def runQemu(self, cmd):
        args = "make hv6-qemu QEMUEXTRA='-device isa-debug-exit -append \"%s\"'" % (
            cmd,)
        try:
            self.output = subprocess.check_output(
                args, shell=True, stderr=DEVNULL)
        except subprocess.CalledProcessError as err:
            self.output = err.output

    def assertRegexpMatches(self, text, expected_regexp, msg=None):
        # patch multiline
        if isinstance(expected_regexp, basestring):
            expected_regexp = re.compile(expected_regexp, re.MULTILINE)
        if not expected_regexp.search(text):
            msg = msg or "Regexp didn't match"
            msg = '%s: %r not found in %r' % (
                msg, expected_regexp.pattern, text)
            raise self.failureException(msg)

    def assertMatch(self, *args):
        for r in args:
            self.assertRegexpMatches(self.output, r)


class TestCmds(TestCase):
    def test_hello(self):
        self.runQemu("hello")
        self.assertMatch(r"^Hello from Linux$")

    def test_ls(self):
        self.runQemu("ls")
        self.assertMatch(r"^\.\s*1\s*1")
        self.assertMatch(r"^\..\s*1\s*1")
        self.assertMatch(r"^README.md\s*2")
        self.assertMatch(r"^console\s*3")


if __name__ == "__main__":
    signal.alarm(30)
    unittest.main()
