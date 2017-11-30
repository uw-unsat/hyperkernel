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

#include "PyEmitter.hh"

#include <sstream>

namespace irpy {

void PyEmitter::genBlock(const std::string &blk, const std::function<void()> &body)
{
    this->line(blk + ":");
    ++indent_level_;
    body();
    --indent_level_;
}

void PyEmitter::genDef(const std::string &name, const std::vector<std::string> &args,
                       const std::function<void()> &func)
{
    std::ostringstream def;
    def << "def " << name << "(";
    for (auto &a : args)
        def << a << ",";
    def << ")";
    this->genBlock(def.str(), func);
    this->line();
}

void PyEmitter::emitWarning(const std::string &filename) const
{
    this->line("#");
    this->line("# WARNING: This file has been automatically generated from " + filename);
    this->line("#");
    this->line();
}

void PyEmitter::genException(const std::string &message) const
{
    this->line("raise Exception('" + message + ")");
    this->line();
}

} // namespace irpy
