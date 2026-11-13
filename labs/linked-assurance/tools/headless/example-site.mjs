#!/usr/bin/env node
// SPDX-License-Identifier: Apache-2.0
// npm install in this directory, then node example-site.mjs.
// This demonstrates an arbitrary site's own names and typed parameters.
import {serveStdio} from '@modelcontextprotocol/server/stdio';
import {defineProfile,createDispatcher} from '../../profile/core.js';
import {mcpFactory} from './mcp-adapter.mjs';
const profile=defineProfile({id:'example-site',transports:['mcp-stdio'],tools:[{
 name:'example_site.describe',description:'Describe an identifier supplied by the caller.',requires:['read-resources'],
 annotations:{readOnlyHint:true,consequentialHint:false},
 inputSchema:{type:'object',properties:{iri:{type:'string',maxLength:1000},includeLength:{type:'boolean',default:true}},required:['iri'],additionalProperties:false}
}]});
const dispatcher=createDispatcher({profile,transport:'mcp-stdio',capabilities:['read-resources'],handlers:{
 'example_site.describe':({iri,includeLength})=>({iri,...(includeLength?{length:[...iri].length}:{})})
}});
await serveStdio(mcpFactory(dispatcher));
