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

void bla(uint32_t x, uint32_t **a, uint32_t *b, uint32_t *c)
{
    if (x > 1 << 31)
        *a = b;
    else
        *a = c;
}

uint32_t test(uint32_t x, uint32_t y, uint32_t z)
{
    uint32_t *a = NULL;
    uint32_t *b = &y;
    uint32_t *c = &z;
    bla(x, &a, b, c);
    return *a;
}

int main(int argc, char **argv)
{
    uint32_t res = test(atoi(argv[1]), atoi(argv[2]), atoi(argv[3]));
    printf("%u\n", res);
    return 0;
}
