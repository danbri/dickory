#!/usr/bin/env node
// SPDX-License-Identifier: Apache-2.0
import {serveStdio} from '@modelcontextprotocol/server/stdio';
import {createServerFactory} from './mcp-factory.mjs';
// SDK 2.4.0 serves MCP 2026-07-28 and optional legacy peers. Tests and CLI
// explicitly PIN 2026-07-28, preventing unnoticed initialize-era fallback.
const handle=await serveStdio(await createServerFactory('mcp-stdio'));
process.on('SIGINT',()=>{void handle.close();});
