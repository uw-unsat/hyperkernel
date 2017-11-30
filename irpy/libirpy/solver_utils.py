#
# Copyright 2017 Hyperkernel Authors
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#

import math
import json

LEN_LEN = 8


def write_cmd(stream, command):
    payload = json.dumps(command)
    assert math.log(
        len(payload), 10) < LEN_LEN, "payload length = {} too large".format(len(payload))
    payload = str(len(payload)).rjust(LEN_LEN, '0') + payload
    stream.write(payload)
    stream.flush()


def read(stream, count):
    v = stream.read(count)
    return v


def read_cmd(stream):
    cmdlen = read(stream, LEN_LEN)
    if not cmdlen:
        return None
    data = read(stream, int(cmdlen))
    try:
        return json.loads(data)
    except Exception, e:
        print "Found exception", e, data
        raise e
