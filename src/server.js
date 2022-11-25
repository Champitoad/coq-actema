import { ipcMain } from 'electron';

const http = require('http');

function parseQueryString(req) {
  return new URL(req.url, `http://${req.headers.host}`);
}

export default {
  launch: function (win) {
    // Create a local server to receive data from
    const server = http.createServer((req, res) => {
      ipcMain.on('action', (_, action) => {
        let rcode = 200;
        res.writeHead(rcode, { 'Content-Type': 'text/plain' });
        res.end(action.subgoalIndex.toString() + "\n" + action.repr);
      });
      ipcMain.on('done', _ => {
        let rcode = 201;
        res.writeHead(rcode, { 'Content-Type': 'text/plain' });
        res.end('');
      });
      ipcMain.on('undo', _ => {
        let rcode = 202;
        res.writeHead(rcode, { 'Content-Type': 'text/plain' });
        res.end('');
      });
      ipcMain.on('redo', _ => {
        let rcode = 203;
        res.writeHead(rcode, { 'Content-Type': 'text/plain' });
        res.end('');
      });
      ipcMain.on('error', (_, msg) => {
        rcode = 550;
        res.writeHead(rcode, { 'Content-Type': 'text/plain' });
        res.end(msg);
      });

      let data = '';
      req.on('data', chunk => {
        data += chunk;
      });
      req.on('end', () => {
        let rcode, body;
        let query = parseQueryString(req);
        switch (query.pathname) {
          case "/action":
            let goals = data;
            win.webContents.send('action', goals);
            break;
          case "/qed":
            win.webContents.send('qed', '');
            rcode = 200;
            res.writeHead(rcode, { 'Content-Type': 'text/plain' });
            res.end('');
            break;
          default:
            rcode = 501;
            body = req.url;
            res.writeHead(rcode, { 'Content-Type': 'text/plain' });
            res.end(body);
            break;
        }
      });
    });
    server.listen(8124, () => {
      console.log('server bound');
    });
  }
}
