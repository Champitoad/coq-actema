import { ipcMain } from 'electron';

const http = require('http');

function parseQueryString(req) {
  return new URL(req.url, `http://${req.headers.host}`);
}

export default {
  launch: function (win) {
    // Create a local server to receive data from
    const server = http.createServer((req, res) => {
      let data = '';
      req.on('data', chunk => {
        data += chunk;
      });
      req.on('end', () => {
        let rcode, body;
        let query = parseQueryString(req);
        switch (query.pathname) {
          case "/action":
            rcode = 200;
            let goal = data;
            win.webContents.send('action', goal);
            res.writeHead(rcode, { 'Content-Type': 'text/plain' });
            ipcMain.on('action', (_, proofb) => {
              res.end(proofb);
            });
            break;
          default:
            rcode = 501;
            body = req.url;
            break;
        }
      });
    });
    server.listen(8124, () => {
      console.log('server bound');
    });
  }
}
