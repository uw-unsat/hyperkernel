/*
 * Copyright 2017 Hyperkernel Authors
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

int test(uint64_t x, uint64_t y)
{
    uint64_t z = 123;
    if (y < 10 && x < y) {
        for (; x < y; x++) {
            z += x * y + z;
        }
    }

    return z;
}

int main(int argc, char **argv)
{
    int res = test(strtoull(argv[1], NULL, 10), strtoull(argv[2], NULL, 10));
    printf("%u\n", res);
    return 0;
}
